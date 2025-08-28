{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-25.05;
    flake-utils.url = github:numtide/flake-utils;
    cabalPlan2nix.url = github:solomon-b/cabalPlan2nix;
  };

  outputs = { self, nixpkgs, flake-utils, cabalPlan2nix }:
    let
      ghcVersion = "963";
      compiler = "ghc${ghcVersion}";
      overlay = import ./overlay.nix;
      overlays = [overlay cabalPlan2nix.overlays.default];
    in
    flake-utils.lib.eachDefaultSystem
      (system:
        let
          pkgs = import nixpkgs { inherit system overlays; };
          inherit (pkgs) lib;  # Import lib
          cabalPlan2nixResult = pkgs.haskell.lib.cabalPlan2nix ./plan.json "/home/solomon/Development/Haskell/monoidal-functors";
        in
        rec {
          devShell = pkgs.mkShell {
            buildInputs = with pkgs; [
              cabal-install
              haskell.compiler.${compiler}
              haskell.packages.${compiler}.haskell-language-server
              nixpkgs-fmt
              ormolu
            ];
          };

          formatter = pkgs.nixpkgs-fmt;
          packages = flake-utils.lib.flattenTree {
            monoidal-functors = pkgs.haskellPackages.monoidal-functors;
            monoidal-functors-with-deps = (pkgs.haskellPackages.override {
              overrides = cabalPlan2nixResult.overlay;
            }).monoidal-functors;
          };

          defaultPackage = packages.monoidal-functors;
        }) // {
      overlays.default = overlay;
    };
}
