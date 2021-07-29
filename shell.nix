let
  sources = import ./nix/sources.nix;
  pkgs = import sources.nixpkgs { };

  editorTooling = [
    pkgs.hlint
    pkgs.cabal-install
    pkgs.cabal2nix
    pkgs.haskell-language-server
  ];

  buildDeps = [ pkgs.haskell.compiler.ghc8104 ];
in
pkgs.mkShell {
  buildInputs = editorTooling ++ buildDeps;
}
