# Revision history for monoidal-functors

## Upcoming
* Adds `Data.Functor.Monoidal.Generic` for deriving `Semigroupal`, `Unital`, and `Monoidal` instances via `kind-generics`. `FromGeneric` covers both covariant (Applicative/Alternative) and contravariant (Divisible/Decidable) functors across the `(,)`, `Either`, and `These` tensors; `FromRepresentable` additionally derives the coherent `Op` split for representable functors.
* Adds `Bifunctor.Monoidal` instances for `Biapplicative`.
* Adds infix operators for `Semigroupal`.
* Adds `Data.Functor.Monoidal.Specialized` combinators module.
* Adds `Biapplicative` operations to `Data.Bifunctor.Monoidal.Specialized`.
* Adds `Unalign` `Semigroupal` instances.
* Expands GHC support through 9.12; bumps nixpkgs, Cabal, and CI tooling.
* Adds support for `semialign` 1.4 (retaining 1.3 compatibility via CPP).
* Replaces the `Makefile` with a `justfile` for local development.

## 0.2.3.0 -- 2023-08-03
* Add support for GHC 9.6

## 0.2.2.0 -- 2023-06-26

* Adds `co-log` example.
* Switch to Ormolu formatting and a `Makefile` to manage local development.
* Remove Arrow terminology from haddocks.
* Adds missing `Star` and `Kleisli` instances.
* Adds `Unital` and `Monoidal` instances for `Divisible` and `Decidable`.

## 0.2.1.0 -- 2023-01-29

* Rewrite `Semigroupal`, `Unital`, and `Monoidal` `Functor` instances
  to use deriving via.

## 0.2.0.0 -- 2023-01-29

* Adds Tensored Type.
* Rewrites haddocks.
* Adds `Control.Category.Cartesian` module.
* Adds a number of specialized combinators to `Data.Bifunctor.Monoidal.Specialized`.

## 0.1.1.0 -- 2021-12-13

* Removes redundant `Iso` types.
* Some initial attempts at documentation.

## 0.1.0.0 -- 2021-04-19

* First version.
