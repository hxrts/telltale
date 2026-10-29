{
  description = "Telltale - Session types for asynchronous communication";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    # Match Aura's compiler derivation without upgrading unrelated packages.
    rust-nixpkgs.url = "github:NixOS/nixpkgs/5e2a59a5b1a82f89f2c7e598302a9cacebb72a67";
    rust-overlay.url = "github:oxalica/rust-overlay";
    flake-utils.url = "github:numtide/flake-utils";
    toolkit = {
      url = "github:hxrts/toolkit?ref=v0.4.2";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.rust-overlay.follows = "rust-overlay";
      inputs.rust-nixpkgs.follows = "rust-nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };
  outputs =
    {
      self,
      nixpkgs,
      rust-overlay,
      rust-nixpkgs,
      flake-utils,
      toolkit,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        overlays = [
          (import rust-overlay)
        ];
        # lean/lean-toolchain is the single source of truth for the Lean release.
        leanToolchain =
          pkgs.lib.strings.removeSuffix "\n" (builtins.readFile ./lean/lean-toolchain);

        pkgs = import nixpkgs {
          inherit system overlays;
        };
        toolkitSupport = toolkit.lib.${system}.consumerShellSupport;

        compilerPkgs = import rust-nixpkgs {
          inherit system overlays;
        };
        rustToolchain = compilerPkgs.rust-bin.stable."1.99.1".default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "clippy"
          ];
          targets = [ "wasm32-unknown-unknown" ];
        };

        # Match Aura's cache executable as well as its compiler input.
        sharedSccache = compilerPkgs.sccache;

        # Cargo searches Cargo-home plugins before PATH. Keep Clippy and fmt on the
        # same exact stable compiler as ordinary builds.
        telltaleCargo = pkgs.writeShellScriptBin "cargo" ''
          set -euo pipefail
          export RUSTC="${rustToolchain}/bin/rustc"
          export RUSTDOC="${rustToolchain}/bin/rustdoc"
          export CARGO="${rustToolchain}/bin/cargo"
          export TELLTALE_NIX_CARGO_BIN="${rustToolchain}/bin/cargo"
          export TELLTALE_NIX_CLIPPY_BIN="${rustToolchain}/bin/cargo-clippy"
          export TELLTALE_NIX_FMT_BIN="${rustToolchain}/bin/cargo-fmt"
          export TELLTALE_NIX_SCCACHE_BIN="${sharedSccache}/bin/sccache"
          export RUSTFMT="${rustToolchain}/bin/rustfmt"
          exec ${pkgs.bash}/bin/bash ${./scripts/dev/cargo-in-nix.sh} "$@"
        '';

        wasmPack = pkgs.rustPlatform.buildRustPackage rec {
          pname = "wasm-pack";
          version = "0.14.0";

          src = pkgs.fetchCrate {
            inherit pname version;
            hash = "sha256-lXxUsj2OFyUReAujBivXGAPBGOcl5rCuj7RnLkKp6sQ=";
          };

          cargoHash = "sha256-n9xuwlj8+3fDTHMS2XobqWFc6mNHQcmmvebRDc82oSo=";
          doCheck = false;

          meta = with pkgs.lib; {
            description = "Tool for building Rust-generated WebAssembly packages";
            homepage = "https://github.com/rustwasm/wasm-pack";
            license = with licenses; [
              asl20
              mit
            ];
            mainProgram = "wasm-pack";
          };
        };

        # LaTeX distribution for paper compilation
        texlive = pkgs.texlive.combine {
          inherit (pkgs.texlive)
            scheme-medium
            latexmk
            biber
            biblatex
            booktabs
            cleveref
            enumitem
            etoolbox
            hyperref
            mathtools
            natbib
            parskip
            pgf
            tikz-cd
            xcolor
            ;
        };

        nativeBuildInputs = with pkgs; [
          telltaleCargo
          rustToolchain
          pkg-config
          gnuplot
          wasmPack
          samply
          mdbook
          mdbook-mermaid
          just
          git
          ripgrep
          jq
          coreutils
          findutils
          gawk
          gnused
          elan
          python3
          texlive
        ] ++ toolkitSupport.packages;

        buildInputs =
          with pkgs;
          [
            openssl
          ]
          ++ lib.optionals stdenv.isDarwin [
            libiconv
          ]
          ++ toolkitSupport.buildInputs;

      in
      {
        devShells.default = pkgs.mkShell {
          inherit nativeBuildInputs buildInputs;

          shellHook = ''
            ${toolkitSupport.shellHook}
            # Match Aura's one local 10G store; targets remain checkout-local.
            # Shell entry exposes tooling but never starts a cache server/build.
            # Nonincremental by default; CARGO_INCREMENTAL=1 is the explicit
            # edit/test opt-in and bypasses sccache per invocation.
            export CARGO_INCREMENTAL="''${CARGO_INCREMENTAL:-0}"
            if [ "''${TELLTALE_NO_SCCACHE:-0}" != 1 ]; then
              export RUSTC_WRAPPER="''${RUSTC_WRAPPER-${sharedSccache}/bin/sccache}"
              export SCCACHE_DIR="''${SCCACHE_DIR:-$HOME/.cache/aura-sccache}"
              export SCCACHE_CACHE_SIZE="''${SCCACHE_CACHE_SIZE:-10G}"
            fi
            export ELAN_TOOLCHAIN="${leanToolchain}"

            # Default Lake's artifact cache on and keep cached artifacts
            # materialized under .lake/build; a caller's explicit value wins.
            export LAKE_ARTIFACT_CACHE="''${LAKE_ARTIFACT_CACHE:-true}"
            export LAKE_RESTORE_ARTIFACTS="''${LAKE_RESTORE_ARTIFACTS:-true}"

            # Let Lake restore prebuilt mathlib artifacts from the shared cache
            # before mathlib's post-update hook downloads them again.
            export MATHLIB_NO_CACHE_ON_UPDATE="''${MATHLIB_NO_CACHE_ON_UPDATE:-1}"

            # Join the machine-local shared artifact cache when a sibling
            # lean-builder checkout provides one. Absent for other contributors,
            # who then get Lake's own default cache.
            if [ -f ../lean-builder/env.sh ]; then
              . ../lean-builder/env.sh
            fi
            [[ -r "$HOME/.local/state/secrets/cargo-registry-token" ]] && export CARGO_REGISTRY_TOKEN="$(cat "$HOME/.local/state/secrets/cargo-registry-token")"

            # Install cargo-based dev tools if missing or outdated
            if ! command -v dx >/dev/null 2>&1; then
              echo "Installing dioxus-cli..."
              cargo install dioxus-cli 2>/dev/null
            fi
            if ! command -v wasm-bindgen >/dev/null 2>&1 || ! wasm-bindgen --version 2>/dev/null | grep -q "0.2.117"; then
              echo "Installing wasm-bindgen-cli 0.2.117..."
              cargo install wasm-bindgen-cli --version 0.2.117 2>/dev/null
            fi

            echo "Telltale development environment"
            echo "Rust: $(rustc --version)"
            echo "Lean: ${leanToolchain}"
            echo "WASM: $(rustc --print target-list | grep wasm32-unknown-unknown || echo 'available')"
            echo "Toolkit: ''${TOOLKIT_ROOT:-unavailable}"
          '';
        };

        packages.default = (pkgs.makeRustPlatform {
          cargo = rustToolchain;
          rustc = rustToolchain;
        }).buildRustPackage {
          pname = "telltale";
          version = "0.1.1-aura";

          src = ./.;

          cargoLock = {
            lockFile = ./Cargo.lock;
            outputHashes = {
              "dioxus-primitives-0.0.1" = "sha256-JrFrhy34UnR1x0qMaT/+x3RoIsOXhAdBj2m8SKNfHug=";
              "dioxus-shadcn-0.3.0" = "sha256-vL/eYDly3uhBr5M5lPCl2uiLTXEOTVJI0MchxicIN0Q=";
            };
          };

          inherit nativeBuildInputs buildInputs;

          meta = with pkgs.lib; {
            description = "Session types for asynchronous communication between multiple parties - Aura fork for threshold cryptography choreographies";
            homepage = "https://github.com/hxrts/telltale";
            license = with licenses; [
              mit
              asl20
            ];
            maintainers = [ ];
          };
        };

        # Paper PDF compilation (all three papers)
        packages.paper = pkgs.stdenvNoCC.mkDerivation {
          pname = "telltale-papers";
          version = "0.1.0";

          src = ./paper;

          nativeBuildInputs = [ texlive ];

          buildPhase = ''
            # Compile each paper twice for references
            for paper in paper1 paper2 paper3; do
              pdflatex -interaction=nonstopmode $paper.tex || true
              pdflatex -interaction=nonstopmode $paper.tex
            done
          '';

          installPhase = ''
            mkdir -p $out
            cp paper1.pdf $out/telltale-paper1-coherence.pdf
            cp paper2.pdf $out/telltale-paper2-dynamics.pdf
            cp paper3.pdf $out/telltale-paper3-harmony.pdf
          '';

          meta = with pkgs.lib; {
            description = "Telltale papers: MPST metatheory series (Coherence, Dynamics, Harmony)";
            license = licenses.cc-by-40;
          };
        };
      }
    );
}
