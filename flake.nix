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

        # Cargo searches Cargo-home plugins before PATH. Keep Clippy on the
        # same exact stable compiler as ordinary builds.
        telltaleCargo = pkgs.writeShellScriptBin "cargo" ''
          set -euo pipefail
          export RUSTC="${rustToolchain}/bin/rustc"
          export RUSTDOC="${rustToolchain}/bin/rustdoc"
          export CARGO="${rustToolchain}/bin/cargo"
          if [ "''${1:-}" = clippy ]; then
            exec ${rustToolchain}/bin/cargo-clippy "$@"
          fi
          exec ${rustToolchain}/bin/cargo "$@"
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
            echo "Lean: $(elan show 2>/dev/null | head -1 || echo 'run: elan default leanprover/lean4:v4.25.0')"
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
