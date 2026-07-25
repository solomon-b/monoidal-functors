Monoidal Functors
=================

[![monoidal-functors::CI](https://github.com/solomon-b/monoidal-functors/actions/workflows/nix.yml/badge.svg)](https://github.com/solomon-b/monoidal-functors/actions/workflows/nix.yml)

A monoidal functor is a functor between monoidal categories that
preserves the monoidal structure.

This library encodes monoidal functors and related structures in
Haskell.

## Testing

There are two test suites:

- `spec` checks the type class laws with hedgehog.
- `doctests` runs the `>>>` examples in the Haddocks with
  [doctest-parallel](https://hackage.haskell.org/package/doctest-parallel).

Run both with:

```sh
cabal test all
```

Run only the doctests with:

```sh
cabal test doctests
```

To run the doctests for a single module, pass its name:

```sh
cabal run doctests -- Control.Category.Cartesian
```

The doctest runner reads the module list and language extensions straight
from the Cabal file, so new modules and examples are picked up without any
extra configuration.
