final: prev: {
  haskellPackages = prev.haskellPackages.override (old: {
    overrides = prev.lib.composeExtensions (old.overrides or (_: _: { }))
      (hfinal: hprev: {
        monoidal-functors = (hfinal.callCabal2nix "monoidal-functors" ./. {}).overrideScope (hfinal': hprev': {
          bifunctors = hfinal.bifunctors_5_6_1;
          semigroupoids = hfinal.semigroupoids_6_0_0_1.overrideScope (hfinal': hprev': {
            bifunctors = hfinal.bifunctors_5_6_1;
          });
        });
      });
  });
}
