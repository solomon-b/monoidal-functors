# Revision history for monoidal-functors

## Upcoming
* Adds `Bifunctor.Monoidal` instances for `Biapplicative`.
* Adds infix operators for `Semigroupal`.
* Adds `Data.Functor.Monoidal.Specialized` combinators module.
* Adds `Biapplicative` operations to `Data.Bifunctor.Monoidal.Specialized`.
* Adds `Unalign` `Semigroupal` instances.

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
