Monoidal Functors
=================

[![monoidal-functors::CI](https://github.com/solomon-b/monoidal-functors/actions/workflows/nix.yml/badge.svg)](https://github.com/solomon-b/monoidal-functors/actions/workflows/nix.yml)

A monoidal functor is a functor between monoidal categories that
preserves the monoidal structure.

This library encodes monoidal functors and related structures in
Haskell.

## Testing

Using Doctest to find all Haskell sources:

```sh
cabal exec -- cabal test
```

or individual files:

```sh
cabal exec -- doctest -isrc -XLambdaCase -XUndecidableInstances -XFunctionalDependencies src/Control/Category/Cartesian.hs
```

TODO: Find out how to enable extensions automatically.
