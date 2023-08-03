{
  description = "Monoidal Functors";

  inputs = {
    nixpkgs.url = github:NixOS/nixpkgs/nixos-23.05;
    flake-utils.url = github:numtide/flake-utils;
  };

  outputs = { self, nixpkgs, flake-utils }:
    let
      ghcVersion = "962";
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
          overrides = hfinal: hprev: with pkgs.haskell.lib.compose; {
            monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
            assoc = hfinal.assoc_1_1;
            bifunctors = hfinal.bifunctors_5_6_1;
            foldable1-classes-compat = dontCheck hprev.foldable1-classes-compat;
            indexed-traversable-instances = dontCheck hprev.indexed-traversable-instances;
            semialign = hfinal.semialign_1_3;
            semigroupoids = hfinal.semigroupoids_6_0_0_1;
            tagged = hfinal.tagged_0_8_7;
            these = hfinal.these_1_2;
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
