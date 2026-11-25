{
  description = "Leanharbor: web services whose core is a kernel proved in Lean";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    treefmt-nix = {
      url = "github:numtide/treefmt-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    leanfran = {
      url = "github:conao3/lean-leanfran/2f50b0093ad9e7712bbcde17cb4fdbf3e217714e";
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
            settings.global.excludes = [
              "rust/calculator/src/generated/*"
              "python/src/leanharbor_calculator/kernel.py"
              "go/calculator/kernel/*"
              "python/src/leanharbor_calculator/store.py"
              "go/calculator/store/*"
              "rust/leanharbor/src/generated/*"
              "python/src/leanharbor/sql.py"
              "go/leanharbor/sql/*"
              "python/src/leanharbor/token_format.py"
              "go/leanharbor/token/*"
              "python/src/leanharbor/json_format.py"
              "go/leanharbor/jsonformat/*"
            ];
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
            pname = "leanharbor-calculator";
            version = "0.1.0";
            src = ./.;
            cargoRoot = "rust";
            buildAndTestSubdir = "rust";
            cargoLock.lockFile = ./rust/Cargo.lock;
            cargoBuildFlags = [
              "--package"
              "leanharbor-calculator"
              "--bin"
              "leanharbor-calculator"
            ];
            doCheck = false;
            meta = {
              mainProgram = "leanharbor-calculator";
              license = pkgs.lib.licenses.asl20;
            };
          };
        };
    };
}
