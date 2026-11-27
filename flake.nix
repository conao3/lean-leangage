{
  description = "Leangage: web services whose core is a kernel proved in Lean";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    leanfran = {
      url = "github:conao3/lean-leanfran/346658a7ae3a3aa0b976952465de1a525fdefe4d";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };
  outputs =
    inputs:
    inputs.flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-darwin"
      ];
      imports = [ inputs.treefmt-nix.flakeModule ];
      perSystem =
        { pkgs, system, ... }:
        let
          leanfran = inputs.leanfran.packages.${system};
        in
        {
          treefmt = {
            projectRootFile = "flake.nix";
            programs.gofmt.enable = true;
            programs.nixfmt.enable = true;
            programs.rustfmt = {
              enable = true;
              edition = "2024";
            };
            programs.ruff-check.enable = true;
            programs.ruff-format.enable = true;
          };
          devShells.default = pkgs.mkShell {
            packages = [
              pkgs.cargo
              pkgs.clippy
              pkgs.gcc
              pkgs.git
              pkgs.gnumake
              pkgs.go
              pkgs.lean4
              pkgs.postgresql
              pkgs.python314
              pkgs.rust-analyzer
              pkgs.rustc
              pkgs.rustfmt
              pkgs.uv
              leanfran.rust-compiler
              leanfran.python
              leanfran.go
            ];
            UV_PYTHON_DOWNLOADS = "never";
          };
          packages.default = pkgs.rustPlatform.buildRustPackage {
            pname = "leangage-calculator";
            version = "0.1.1";
            src = ./.;
            cargoRoot = "rust";
            buildAndTestSubdir = "rust";
            cargoLock.lockFile = ./rust/Cargo.lock;
            nativeBuildInputs = [
              pkgs.lean4
              leanfran.rust-compiler
            ];
            preBuild = ''
              make generate-rust
            '';
            cargoBuildFlags = [
              "--package"
              "leangage-calculator"
              "--bin"
              "leangage-calculator"
            ];
            doCheck = false;
            meta = {
              mainProgram = "leangage-calculator";
              license = pkgs.lib.licenses.asl20;
            };
          };
        };
    };
}
