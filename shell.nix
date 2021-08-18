let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs { };

  easy-hls = pkgs.callPackage sources.easy-hls-nix {
    ghcVersions = [ "8.10.4" ];
  };

  editorTooling = [
    pkgs.hlint
    pkgs.cabal-install
    pkgs.cabal2nix
    easy-hls
  ];

  buildDeps = [ pkgs.haskell.compiler.ghc8104 ];
in
pkgs.mkShell {
  buildInputs = editorTooling ++ buildDeps;
}
