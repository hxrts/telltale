use telltale_macros::choreography;

choreography!(r#"
protocol Broadcast =
  roles Leader, Worker1, Worker2
  Leader ->* : Start
"#);

fn main() {
    let _roles = setup();
}
