{
  description = "Tiny C reference compilation for learnability pipeline analysis";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        packages = with pkgs; [
          gcc
          binutils
        ];
        shellHook = ''
          echo "tinyc-reference build environment"
          echo "gcc: $(gcc --version | head -1)"
          echo "objdump: $(objdump --version | head -1)"
        '';
      };
    };
}
