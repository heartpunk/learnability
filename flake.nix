{
  description = "learnability VEX reference environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    angr-nix.url = "github:heartpunk/angr-nix/2f20f9ed68506bd151ed171e505942ac9a2a0b43";
    stalagmite = {
      url = "github:leonbett/stalagmite/eadeecfd0845859e78d7390270a7bee31f57bc71";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, lean4-nix, angr-nix, stalagmite }:
    let
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f system);
    in {
      devShells = forAllSystems (system:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
        in {
          default = pkgs.mkShell {
            packages = [
              pkgs.lean
              angr-nix.packages.${system}.default
              pkgs.git
              pkgs.jujutsu
              pkgs.uv
              pkgs.jq
              pkgs.cvc5
              pkgs.just
            ] ++ pkgs.lib.optionals pkgs.stdenv.isLinux [
              pkgs.gcc
              pkgs.binutils
              pkgs.boehmgc
            ];
            env = {
              UV_NO_MANAGED_PYTHON = "1";
              UV_PYTHON_DOWNLOADS = "never";
            };
          };
        });
    };
}
