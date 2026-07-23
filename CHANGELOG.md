# Revision history for monoidal-functors

## Upcoming
* Reworks the `Semigroupal` / `Unital` / `Monoidal` instances for `Product`, `f :*: g`, the transparent newtype wrappers (`Rec1`, `M1`, `Alt`, `Reverse`, `Backwards`), and the phantom functors (`Proxy`, `U1`, `Const`, `Constant`) into single variance-agnostic instances that hold at every tensor and both variances at once, removing the previous covariant/contravariant instance overlaps. `Product` and `:*:` combine componentwise by delegating to their components' own instances; the wrappers inherit their component's instance by coercion; and the phantom functors combine via their underlying `Semigroup` (`Const` / `Constant`) or the trivial value (`Proxy` / `U1`). As a result `Product`/`:*:`/wrappers are now usable with contravariant components (e.g. `Product Predicate Comparison`), which previously did not typecheck.
* Adds `Data.Functor.Monoidal.Generic` for deriving `Semigroupal`, `Unital`, and `Monoidal` instances via `kind-generics`. `FromGeneric` covers both covariant (Applicative/Alternative) and contravariant (Divisible/Decidable) functors across the `(,)`, `Either`, and `These` tensors; `FromRepresentable` additionally derives the coherent `Op` split for representable functors.
* Adds a `monoidal-functors:laws` public sublibrary exporting `hedgehog-classes` `Laws` for the monoidal-functor classes, so consumers can law-test their own instances. Covers covariant functors (`semigroupalLaws` / `unitalLaws` / `monoidalLaws`, compared with `Eq`), contravariant functors (`contravariantSemigroupalLaws` / `contravariantUnitalLaws` / `contravariantMonoidalLaws`, checked extensionally through an observation), and the `Op` comonoidal split (`opSemigroupalLaws`, plus `representableSplitLaws` for split/combine coherence). Requires `cabal-version: 3.0`.
* Adds `Control.Category.Tensor.Laws` and `Control.Category.Cartesian.Laws` to the `monoidal-functors:laws` sublibrary — reusable `hedgehog-classes` `Laws` for the categorical structure classes (`gbifunctorLaws`, `isoLaws`, `associativeLaws`, `tensorLaws`, `symmetricLaws`, `semicartesianLaws`, `semicocartesianLaws`, `cartesianLaws`, `cocartesianLaws`) so consumers can law-test their own instances. Each law is checked extensionally through a caller-supplied observer, so it holds at any category (`(->)`, `Op`, `Star` / `Kleisli`, …).
* Adds `Data.Bifunctor.Monoidal.Laws` to the `monoidal-functors:laws` sublibrary — `semigroupalLaws` / `unitalLaws` / `monoidalLaws` for covariant bifunctor `Monoidal` instances (compared with `Eq`), and `profunctorSemigroupalLaws` / `profunctorUnitalLaws` / `profunctorMonoidalLaws` for profunctor instances (`(->)`, `Star`, `Kleisli`, …, observed extensionally). The bifunctor analog of `Data.Functor.Monoidal.Laws`.
* Adds `Bifunctor.Monoidal` instances for `Biapplicative`.
* Adds infix operators for `Semigroupal`.
* Adds `Data.Functor.Monoidal.Specialized` combinators module.
* Adds `Biapplicative` operations to `Data.Bifunctor.Monoidal.Specialized`.
* Adds `Unalign` `Semigroupal` instances.
* Expands GHC support through 9.12; bumps nixpkgs, Cabal, and CI tooling.
* Adds support for `semialign` 1.4 (retaining 1.3 compatibility via CPP).
* Replaces the `Makefile` with a `justfile` for local development.
* Adds release commands to `justfile`.

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
