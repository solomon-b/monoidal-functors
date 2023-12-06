{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      overlay = import ./overlay.nix;
      overlays = [ overlay ];
    in
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system overlays; };
      in rec {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            pkgs.haskellPackages.cabal-install
            pkgs.haskellPackages.ghc
            pkgs.haskellPackages.haskell-language-server
            nixpkgs-fmt
            ormolu
          ];
        };

        formatter = pkgs.nixpkgs-fmt;
        packages = flake-utils.lib.flattenTree {
          monoidal-functors = pkgs.haskellPackages.monoidal-functors;
        };

        defaultPackage = packages.monoidal-functors;
      }) // {
      overlays.default = overlay;
      };
}
