final: prev: {
  haskellPackages = prev.haskellPackages.override (old: {
    overrides = prev.lib.composeExtensions (old.overrides or (_: _: { }))
      (hfinal: hprev: {
        kindly-functors = hfinal.callCabal2nix "kindly-functors" (final.fetchFromGitHub {
          owner = "solomon-b";
          repo = "kindly-functors";
          rev = "b69c4d7240e0c40da61be522410e8ffc8880f80d";
          sha256 = "sha256-bQvG60Pa8+6NbJWGOCv605XjEraHn0LZHQ4sSC5qtbg=";
        }) {};
        monoidal-functors = (hfinal.callCabal2nix "monoidal-functors" ./. { }).overrideScope (hfinal': hprev': {
          bifunctors = hfinal.bifunctors_5_6_1;
          semigroupoids = hfinal.semigroupoids_6_0_0_1.overrideScope (hfinal': hprev': {
            bifunctors = hfinal.bifunctors_5_6_1;
          });
        });
      });
  });
}
