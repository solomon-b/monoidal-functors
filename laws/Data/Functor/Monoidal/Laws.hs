{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Reusable @hedgehog-classes@ 'Laws' for this library's monoidal-functor
-- classes, so a consumer can law-test their own 'Semigroupal' \/ 'Unital' \/
-- 'Monoidal' instances the same way they test 'Monoid' or 'Applicative':
--
-- > import Data.Functor.Monoidal.Laws (monoidalLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (monoidalLaws @(,) @() genMyFunctor)
--
-- Each law is stated at category @(->)@ over the product domain tensor @(,)@,
-- general in the codomain tensor @t1@ (and, for the unit laws, its unit @i1@),
-- so one function covers whichever tensor an instance uses — @(,)@ (Applicative
-- \/ Divisible), @Either@ (Alternative \/ Decidable), or @These@ (Semialign).
--
-- Both variances and both directions are supported. The 'semigroupalLaws' \/
-- 'unitalLaws' \/ 'monoidalLaws' family is for /covariant/ functors ('Functor'),
-- which are compared directly with 'Eq'. The @contravariant*@ family is for
-- /contravariant/ functors ('Data.Functor.Contravariant.Contravariant', e.g.
-- @Divisible@ \/ @Decidable@), which generally have no 'Eq' \/ 'Show'; those
-- laws are checked extensionally by observing the two sides on a generated
-- input through a caller-supplied @obs :: forall a. f a -> a -> r@. Finally
-- 'opSemigroupalLaws' covers the @'Op'@ (comonoidal) direction — the product
-- split @f (a, b) -> (f a, f b)@.
--
-- The rank-2 generator @forall x. 'Gen' x -> 'Gen' (f x)@ lets a covariant law
-- instantiate @f@ at the several element types the coherence square needs.
module Data.Functor.Monoidal.Laws
  ( -- * Covariant functors
    semigroupalLaws,
    unitalLaws,
    monoidalLaws,

    -- * Contravariant functors
    contravariantSemigroupalLaws,
    contravariantUnitalLaws,
    contravariantMonoidalLaws,

    -- * The Op (comonoidal) laxator
    opSemigroupalLaws,
  )
where

import Control.Category.Tensor (Associative (..), GBifunctor (gbimap), Iso (..), Tensor (..))
import Data.Functor.Contravariant (Contravariant (..), Op (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Hedgehog (Gen, Property, forAll, forAllWith, property, (===))
import Hedgehog.Classes (Laws (..))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Prelude

-- | The element type the coherence squares are witnessed at.
genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

genPair :: Gen a -> Gen b -> Gen (a, b)
genPair ga gb = (,) <$> ga <*> gb

-- | 'combine' laws: it commutes with the codomain tensor's associator
-- (associativity) and with maps into it (naturality of the laxator).
semigroupalLaws ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
semigroupalLaws genF =
  Laws
    "Semigroupal"
    [ ("Associativity", semigroupalAssoc @t1 genF),
      ("Naturality", semigroupalNaturality @t1 genF)
    ]

semigroupalNaturality ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalNaturality genF = property $ do
  x <- forAll (genF genInt)
  y <- forAll (genF genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  fmap (gbimap @(->) @(->) @(->) @t1 g h) (combine @(->) @t1 @(,) (x, y))
    === combine @(->) @t1 @(,) (fmap g x, fmap h y)

semigroupalAssoc ::
  forall t1 f.
  ( Semigroupal (->) t1 (,) f,
    Associative (->) t1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
semigroupalAssoc genF = property $ do
  x <- forAll (genF genInt)
  y <- forAll (genF genInt)
  z <- forAll (genF genInt)
  fmap (bwd (assoc @(->) @t1)) (combine @(->) @t1 @(,) (combine @(->) @t1 @(,) (x, y), z))
    === combine @(->) @t1 @(,) (x, combine @(->) @t1 @(,) (y, z))

-- | Left and right unit laws: 'introduce' is a unit for 'combine', up to the
-- codomain tensor's unitors.
unitalLaws ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
unitalLaws genF =
  Laws
    "Unital"
    [ ("Left Unit", unitalLeft @t1 @i1 genF),
      ("Right Unit", unitalRight @t1 @i1 genF)
    ]

unitalLeft ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalLeft genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitl @(->) @t1)) (combine @(->) @t1 @(,) (introduce @(->) @i1 @() (), fa)) === fa

unitalRight ::
  forall t1 i1 f.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Tensor (->) t1 i1,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
unitalRight genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitr @(->) @t1)) (combine @(->) @t1 @(,) (fa, introduce @(->) @i1 @() ())) === fa

-- | Every 'semigroupalLaws' and 'unitalLaws' property together, for a full
-- 'Monoidal' instance.
monoidalLaws ::
  forall t1 i1 f.
  ( Monoidal (->) t1 i1 (,) () f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
monoidalLaws genF =
  Laws
    "Monoidal"
    ( lawsProperties (semigroupalLaws @t1 genF)
        <> lawsProperties (unitalLaws @t1 @i1 genF)
    )

-- | Laws for the /Op/ (comonoidal) laxator @'combine' \@'Op'@ — the product
-- split @f (a, b) -> (f a, f b)@ that @FromGeneric@ \/ @FromRepresentable@
-- derive. Dual to 'semigroupalLaws': the split is coassociative and natural.
-- Covariant functors only, since the split is an @fmap@-based unzip.
opSemigroupalLaws ::
  forall f.
  ( Semigroupal Op (,) (,) f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Laws
opSemigroupalLaws genF =
  Laws
    "Semigroupal (Op)"
    [ ("Coassociativity", opCoassoc genF),
      ("Conaturality", opConaturality genF)
    ]

opCoassoc ::
  forall f.
  ( Semigroupal Op (,) (,) f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
opCoassoc genF = property $ do
  w <- forAll (genF (genPair genInt (genPair genInt genInt)))
  let split :: forall x y. f (x, y) -> (f x, f y)
      split = getOp (combine @Op @(,) @(,))
      (fa, fbc) = split w
      (fb, fc) = split fbc
      (fab, fc') = split (fmap (fwd (assoc @(->) @(,))) w)
      (fa', fb') = split fab
  ((fa, fb), fc) === ((fa', fb'), fc')

opConaturality ::
  forall f.
  ( Semigroupal Op (,) (,) f,
    Functor f,
    forall x. (Eq x) => Eq (f x),
    forall x. (Show x) => Show (f x)
  ) =>
  (forall x. Gen x -> Gen (f x)) ->
  Property
opConaturality genF = property $ do
  w <- forAll (genF (genPair genInt genInt))
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
      split :: forall x y. f (x, y) -> (f x, f y)
      split = getOp (combine @Op @(,) @(,))
      (fa, fb) = split w
  split (fmap (gbimap @(->) @(->) @(->) @(,) g h) w) === (fmap g fa, fmap h fb)

-- | 'combine' laws for a /contravariant/ functor: associativity and naturality
-- of the laxator. Since contravariant functors (@Divisible@, @Decidable@)
-- generally are not 'Eq' \/ 'Show', the two sides are observed through @obs@ on
-- a generated element of the codomain tensor. @genT@ is a tensor builder — e.g.
-- @\\ga gb -> (,) '<$>' ga '<*>' gb@ for @(,)@, or
-- @\\ga gb -> 'Gen.choice' [Left '<$>' ga, Right '<$>' gb]@ for @Either@ — from
-- which the associativity and naturality observation points are assembled.
contravariantSemigroupalLaws ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantSemigroupalLaws genF genT obs =
  Laws
    "Semigroupal"
    [ ("Associativity", contravariantAssoc @t1 genF genT obs),
      ("Naturality", contravariantNaturality @t1 genF genT obs)
    ]

contravariantAssoc ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantAssoc genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  z <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt (genT genInt genInt))
  obs (contramap (fwd (assoc @(->) @t1)) (combine @(->) @t1 @(,) (combine @(->) @t1 @(,) (x, y), z))) t
    === obs (combine @(->) @t1 @(,) (x, combine @(->) @t1 @(,) (y, z))) t

contravariantNaturality ::
  forall t1 f r.
  ( Semigroupal (->) t1 (,) f,
    Contravariant f,
    Associative (->) t1,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantNaturality genF genT obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  y <- forAllWith (const "<opaque>") genF
  t <- forAll (genT genInt genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  obs (contramap (gbimap @(->) @(->) @(->) @t1 g h) (combine @(->) @t1 @(,) (x, y))) t
    === obs (combine @(->) @t1 @(,) (contramap g x, contramap h y)) t

-- | Left and right unit laws for a /contravariant/ functor, observed through
-- @obs@ at a generated element. The unit laws need no tensor-shaped input.
contravariantUnitalLaws ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantUnitalLaws genF obs =
  Laws
    "Unital"
    [ ("Left Unit", contravariantUnitL @t1 @i1 genF obs),
      ("Right Unit", contravariantUnitR @t1 @i1 genF obs)
    ]

contravariantUnitL ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitL genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitl @(->) @t1)) (combine @(->) @t1 @(,) (introduce @(->) @i1 @() (), x))) a
    === obs x a

contravariantUnitR ::
  forall t1 i1 f r.
  ( Semigroupal (->) t1 (,) f,
    Unital (->) i1 () f,
    Contravariant f,
    Tensor (->) t1 i1,
    Eq r,
    Show r
  ) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contravariantUnitR genF obs = property $ do
  x <- forAllWith (const "<opaque>") genF
  a <- forAll genInt
  obs (contramap (bwd (unitr @(->) @t1)) (combine @(->) @t1 @(,) (x, introduce @(->) @i1 @() ()))) a
    === obs x a

-- | Every 'contravariantSemigroupalLaws' and 'contravariantUnitalLaws' property
-- together, for a full contravariant 'Monoidal' instance.
contravariantMonoidalLaws ::
  forall t1 i1 f r.
  ( Monoidal (->) t1 i1 (,) () f,
    Contravariant f,
    Eq r,
    Show r,
    forall a b. (Show a, Show b) => Show (t1 a b)
  ) =>
  Gen (f Int) ->
  (forall a b. Gen a -> Gen b -> Gen (t1 a b)) ->
  (forall a. f a -> a -> r) ->
  Laws
contravariantMonoidalLaws genF genT obs =
  Laws
    "Monoidal"
    ( lawsProperties (contravariantSemigroupalLaws @t1 genF genT obs)
        <> lawsProperties (contravariantUnitalLaws @t1 @i1 genF obs)
    )
