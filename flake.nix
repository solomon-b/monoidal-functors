{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-22.11;

    flake-utils = {
      url = github:numtide/flake-utils;
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      ghcVersion = "924";
      compiler = "ghc${ghcVersion}";
      # default systems compatible with pre-commit-hooks.nix
      # https://github.com/cachix/pre-commit-hooks.nix/pull/122
      defaultSystems = [
        "aarch64-linux"
        # "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
    in
    flake-utils.lib.eachSystem defaultSystems (system:
      let
        pkgs = import nixpkgs { inherit system; };

        hsPkgs = pkgs.haskell.packages.${compiler}.override {
          overrides = hfinal: hprev: {
            monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
          };
        };
      in
      rec {
        devShell = pkgs.mkShell {
          withHoogle = true;
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
