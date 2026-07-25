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
                kindly-functors = hfinal.callCabal2nix "kindly-functors" (pkgs.fetchFromGitHub {
                  owner = "solomon-b";
                  repo = "kindly-functors";
                  rev = "693a785a085221c1f68a794439556f239ef1499f";
                  sha256 = "sha256-XCqC/5X3cRIN0UHnO0P4wQxzEgEPuQyQcQEurEtNdbY=";
                }) {};
                monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
              });
          });
        in
        {
          devShells.default = pkgs.mkShell {
            buildInputs = with pkgs; [
              cabal-install
              haskell.compiler.${compiler}
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
