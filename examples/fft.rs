//! Eight-role radix-2 FFT butterfly network as a multiparty session type.
//!
//! Eight participants (P0..P7) each hold one complex input value and exchange
//! data through the three butterfly stages of an 8-point FFT. The communication
//! topology follows the standard Cooley-Tukey bit-reversal pattern, with each
//! stage pairing roles at increasing stride distances.
//!
//! This is a projection-surface example: `tell!` owns the butterfly exchange
//! topology, while Rust provides the host-side complex arithmetic and local
//! twiddle/butterfly computation.

use futures::{executor, try_join};
use num_complex::{Complex, Complex32};
use std::{
    error::Error,
    f32::consts::PI,
    fmt::{self, Display, Formatter},
    result,
};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

tell! {
    -- // Stage 1 exchanges values between adjacent butterfly partners.
    protocol FFT =
      roles P0, P1, P2, P3, P4, P5, P6, P7
      P0 -> P1 : Value(num_complex::Complex32)
      P1 -> P0 : Value(num_complex::Complex32)
      P2 -> P3 : Value(num_complex::Complex32)
      P3 -> P2 : Value(num_complex::Complex32)
      P4 -> P5 : Value(num_complex::Complex32)
      P5 -> P4 : Value(num_complex::Complex32)
      P6 -> P7 : Value(num_complex::Complex32)
      P7 -> P6 : Value(num_complex::Complex32)
      -- // Stage 2 exchanges values at stride two.
      P0 -> P2 : Value(num_complex::Complex32)
      P2 -> P0 : Value(num_complex::Complex32)
      P1 -> P3 : Value(num_complex::Complex32)
      P3 -> P1 : Value(num_complex::Complex32)
      P4 -> P6 : Value(num_complex::Complex32)
      P6 -> P4 : Value(num_complex::Complex32)
      P5 -> P7 : Value(num_complex::Complex32)
      P7 -> P5 : Value(num_complex::Complex32)
      -- // Stage 3 exchanges values at stride four to complete the FFT network.
      P0 -> P4 : Value(num_complex::Complex32)
      P4 -> P0 : Value(num_complex::Complex32)
      P1 -> P5 : Value(num_complex::Complex32)
      P5 -> P1 : Value(num_complex::Complex32)
      P2 -> P6 : Value(num_complex::Complex32)
      P6 -> P2 : Value(num_complex::Complex32)
      P3 -> P7 : Value(num_complex::Complex32)
      P7 -> P3 : Value(num_complex::Complex32)
}

use FFT::sessions::*;

/// Twiddle factor: exp(-2πi·k/8).
fn twiddle(k: usize) -> Complex32 {
    #[allow(clippy::as_conversions)]
    let kf = k as f32;
    (-2.0 * PI * Complex::i() * kf / 8.0).exp()
}

/// Butterfly operation applied after exchanging values with a partner.
///
/// `i` is the role index, `stage` is 0/1/2, `x` is our value, `y` is the
/// partner's value.
fn butterfly(i: usize, stage: usize, x: Complex32, y: Complex32) -> Complex32 {
    let twiddle_index = match stage {
        0 => 0,
        1 => 2 * (i % 2),
        2 => i % 4,
        _ => unreachable!(),
    };
    let w = twiddle(twiddle_index);
    if i & (1 << stage) == 0 {
        x + w * y
    } else {
        y - w * x
    }
}

// ---------------------------------------------------------------------------
// Per-role process functions
//
// Each role's session type is projected from the global choreography. In each
// stage the lower-indexed partner sends first (send-recv) and the higher-
// indexed partner receives first (recv-send). The butterfly computation is
// identical regardless of send/receive order.
// ---------------------------------------------------------------------------

async fn process_p0(role: &mut P0, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P0Session<'_, _>| async {
        // Stage 1: P0 sends first to P1
        let s = s.send(Value(input)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(0, 0, input, y);

        // Stage 2: P0 sends first to P2
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(0, 1, x, y);

        // Stage 3: P0 sends first to P4
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(0, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p1(role: &mut P1, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P1Session<'_, _>| async {
        // Stage 1: P1 receives first from P0
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(input)).await?;
        let x = butterfly(1, 0, input, y);

        // Stage 2: P1 sends first to P3
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(1, 1, x, y);

        // Stage 3: P1 sends first to P5
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(1, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p2(role: &mut P2, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P2Session<'_, _>| async {
        // Stage 1: P2 sends first to P3
        let s = s.send(Value(input)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(2, 0, input, y);

        // Stage 2: P2 receives first from P0
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(2, 1, x, y);

        // Stage 3: P2 sends first to P6
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(2, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p3(role: &mut P3, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P3Session<'_, _>| async {
        // Stage 1: P3 receives first from P2
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(input)).await?;
        let x = butterfly(3, 0, input, y);

        // Stage 2: P3 receives first from P1
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(3, 1, x, y);

        // Stage 3: P3 sends first to P7
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(3, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p4(role: &mut P4, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P4Session<'_, _>| async {
        // Stage 1: P4 sends first to P5
        let s = s.send(Value(input)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(4, 0, input, y);

        // Stage 2: P4 sends first to P6
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(4, 1, x, y);

        // Stage 3: P4 receives first from P0
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(4, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p5(role: &mut P5, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P5Session<'_, _>| async {
        // Stage 1: P5 receives first from P4
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(input)).await?;
        let x = butterfly(5, 0, input, y);

        // Stage 2: P5 sends first to P7
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(5, 1, x, y);

        // Stage 3: P5 receives first from P1
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(5, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p6(role: &mut P6, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P6Session<'_, _>| async {
        // Stage 1: P6 sends first to P7
        let s = s.send(Value(input)).await?;
        let (Value(y), s) = s.receive().await?;
        let x = butterfly(6, 0, input, y);

        // Stage 2: P6 receives first from P4
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(6, 1, x, y);

        // Stage 3: P6 receives first from P2
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(6, 2, x, y);

        Ok((x, s))
    })
    .await
}

async fn process_p7(role: &mut P7, input: Complex32) -> Result<Complex32> {
    try_session(role, |s: P7Session<'_, _>| async {
        // Stage 1: P7 receives first from P6
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(input)).await?;
        let x = butterfly(7, 0, input, y);

        // Stage 2: P7 receives first from P5
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(7, 1, x, y);

        // Stage 3: P7 receives first from P3
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        let x = butterfly(7, 2, x, y);

        Ok((x, s))
    })
    .await
}

struct Vector<'a>(&'a [Complex32]);

impl Display for Vector<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;

        if !self.0.is_empty() {
            writeln!(f)?;
            for x in self.0 {
                writeln!(f, "    {x:.3},")?;
            }
        }

        write!(f, "]")
    }
}

fn main() -> Result<()> {
    let Roles(mut p0, mut p1, mut p2, mut p3, mut p4, mut p5, mut p6, mut p7) = Roles::default();

    // Bit-reversed input order for Cooley-Tukey FFT
    let input = [1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
    let input = input.iter().map(Complex::from).collect::<Vec<_>>();
    println!("input = {}", Vector(&input));

    let (o0, o1, o2, o3, o4, o5, o6, o7) = executor::block_on(async {
        try_join!(
            process_p0(&mut p0, input[0]),
            process_p1(&mut p1, input[4]),
            process_p2(&mut p2, input[2]),
            process_p3(&mut p3, input[6]),
            process_p4(&mut p4, input[1]),
            process_p5(&mut p5, input[5]),
            process_p6(&mut p6, input[3]),
            process_p7(&mut p7, input[7]),
        )
    })?;

    let output = [o0, o1, o2, o3, o4, o5, o6, o7];
    println!("output = {}", Vector(&output));
    Ok(())
}
