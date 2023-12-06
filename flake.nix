{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.11;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      ghcVersion = "948";
      compiler = "ghc${ghcVersion}";
    in
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        hsPkgs = pkgs.haskell.packages.${compiler}.override {
          overrides = hfinal: hprev: with pkgs.haskell.lib.compose; {
            monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
            bifunctors = hfinal.bifunctors_5_6_1;
            semigroupoids = hfinal.semigroupoids_6_0_0_1;
          };
        };
      in
      rec {
        devShell = pkgs.mkShell {
          buildInputs = with pkgs; [
            cabal2nix
            cabal-install
            ghcid
            haskell.compiler.${compiler}
            haskell.packages.${compiler}.haskell-language-server
            nixpkgs-fmt
            ormolu
          ];
        };

        packages = flake-utils.lib.flattenTree {
          monoidal-functors = hsPkgs.monoidal-functors;
        };

        defaultPackage = packages.monoidal-functors;
      });
}
