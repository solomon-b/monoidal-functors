{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-26.05;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      ghcVersion = "9103";
      compiler = "ghc${ghcVersion}";
    in
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system; };
          hsPkgs = pkgs.haskell.packages.${compiler}.override (old: {
            overrides = pkgs.lib.composeExtensions (old.overrides or (_: _: { }))
              (hfinal: hprev: {
                kindly-functors = hfinal.callHackageDirect {
                  pkg = "kindly-functors";
                  ver = "0.2.0.0";
                  sha256 = "sha256-pKhloiSuZeomzYq+NXFot5Zd0zaKfapXtF7q9lJXe3g=";
                } {};
                monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
              });
          });
        in
        {
          devShells.default = pkgs.mkShell {
            buildInputs = with pkgs; [
              cabal-install
              haskell.compiler.${compiler}
              haskell.packages.${compiler}.doctest
              haskell.packages.${compiler}.haskell-language-server
              just
              nixpkgs-fmt
              ormolu
            ];
          };

          formatter = pkgs.nixpkgs-fmt;
          packages = flake-utils.lib.flattenTree
            {
              monoidal-functors = hsPkgs.monoidal-functors;
            } // {
            default = hsPkgs.monoidal-functors;
          };
        });
}
