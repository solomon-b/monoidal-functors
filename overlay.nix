compiler: final: prev: {
  haskellPackages = prev.haskell.packages.${compiler}.override (old: {
    overrides = prev.lib.composeExtensions (old.overrides or (_: _: { }))
      (hfinal: hprev: {
        kindly-functors = hfinal.callCabal2nix "kindly-functors" (final.fetchFromGitHub {
          owner = "solomon-b";
          repo = "kindly-functors";
          rev = "26fdb99ef92124241e38e6f4511961ad2f9fb920";
          sha256 = "sha256-nZHERb1QA3XtRZWEcIoq8P4atOBioE7cRrJqrjkw9m0=";
        }) {};
        monoidal-functors = hfinal.callCabal2nix "monoidal-functors" ./. { };
      });
  });
}
