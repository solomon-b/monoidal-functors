# Revision history for monoidal-functors

## Upcoming
* Renames the tensor and unit type parameters of the `Semigroupal` / `Unital` / `Monoidal` and `*.Module` classes to match the Haddock math. Domain tensors and units are `tC` / `iC` (numbered `tC1`, `tC2`, `tC3` per argument for bifunctors and trifunctors), and codomain ones are `tD` / `iD`. This replaces the mix of `t1` / `t0` / `to` / `o`. The parameter order is the same, so visible type applications do not change.
* Makes the `Semigroupal` / `Unital` / `Monoidal` instances for `Data.Bifunctor.Product` componentwise. Each instance delegates to the components' own instances at every tensor and unit, and replaces the `FromBiapplicative` instance that needed `Biapplicative` components. `Product` is now `Monoidal` at profunctor components (e.g. `Product (->) (Star Maybe)`) and at the `Either` and `These` tensors.
* Adds `Data.Bifunctor.Rank2.Monoidal`, the bifunctor-interpreted counterpart to `Data.Functor.Rank2.Monoidal`. A rank-2 bifunctor is a functor from the bifunctor category to `Hask`, so the record's fields have the shape `p a b` as in `Data.Bifunctor.Rank2.Traversable`. Unlike `Data.Bifunctor.Monoidal` the classes take a single domain tensor. A bifunctor's domain is a product category and so needs a pair of tensors, but the bifunctor category is one category. Ships `GHC.Generics` derivations at three instantiations, over `Data.Bifunctor.Product` and `Data.Bifunctor.Sum`: the covariant product (field-wise `Pair`, as the empty-instance default), the coproduct (`gcombineSum`, injecting a whole record all-`L2` or all-`R2`), and the oplax product split (`gsplitProduct`). The tensor units are `Joker Proxy` and `Joker V1`, since `bifunctors` ships no unit or empty bifunctor of its own. There is no `These` instantiation, as the ecosystem has no bifunctor analogue of `These1`.
* Adds rank-2 `Traversable` classes for higher-kinded data: `Data.Functor.Rank2.Traversable`, `Data.Bifunctor.Rank2.Traversable`, and `Data.Trifunctor.Rank2.Traversable`. Their `sequence` distributes the interpretation functor out of a record over any functor / profunctor / trifunctor that is `Monoidal` with respect to tupling. Each ships a `GHC.Generics` default covering records of `f a` / `p a b` / `p a b c` fields, and each is polymorphic over the variance of every interpretation position, generalizing `barbies`' `TraversableB`. The functor version is the `Applicative` collect at a covariant interpretation and the `Divisible` fold at a contravariant one. The bifunctor version splits each field into its `First` and `Second` projections, giving a profunctor traversal at variance `(Op, (->))` and the `Biapplicative` unzip at `((->), (->))`. The trifunctor version splits into `First`, `Second`, and `Third` across its three positions.
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
* Replaces the `doctest-parallel` test-suite with the canonical `cabal repl --with-compiler=doctest` invocation, exposed as `just doctest` and as its own CI job. The old suite reached the library through a shared GHC environment file, which `cabal test all` could rewrite while the suite was running, so any pending rebuild failed the doctests with missing dependencies. Driving `doctest` as the compiler also passes the library's real `ghc-options` and CPP macros, which retires the hand-rolled `MIN_VERSION_semialign` reconstruction and picks up examples the old suite was skipping.
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
