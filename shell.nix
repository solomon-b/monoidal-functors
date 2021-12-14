{ pkgs ? import <nixpkgs> {} }:
let
  easy-hls-src = pkgs.fetchFromGitHub {
    owner  = "jkachmar";
    repo   = "easy-hls-nix";
    rev    = "7c123399ef8a67dc0e505d9cf7f2c7f64f1cd847";
    sha256 = "sha256-/crlHEVB148PGQLZCsHOR9L5qgvCAfRSocIoKgmMAhA=";
  };

  easy-hls = pkgs.callPackage easy-hls-src {
    ghcVersions = [ "8.10.7" ];
  };

  editorTooling = [
    pkgs.cabal-install
    pkgs.ghcid
    easy-hls
  ];

  buildDeps = [ pkgs.haskell.compiler.ghc8107 ];
in
pkgs.mkShell {
  buildInputs = editorTooling ++ buildDeps;
}
