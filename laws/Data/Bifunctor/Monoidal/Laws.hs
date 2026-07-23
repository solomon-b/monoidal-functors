{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Reusable @hedgehog-classes@ 'Laws' for the /covariant/ bifunctor
-- 'Semigroupal' \/ 'Unital' \/ 'Monoidal' classes of
-- "Data.Bifunctor.Monoidal", so a consumer can law-test their own instances the
-- same way they test 'Monoid' or 'Applicative':
--
-- > import Data.Bifunctor.Monoidal.Laws (monoidalLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (monoidalLaws @(,) @() @(,) @() genMyBifunctor)
--
-- Each law is stated at category @('->')@ over the /product/ domain tensor
-- @(,)@, general in the two codomain tensors @t1@ \/ @t2@ (and, for the unit
-- laws, their units @i1@ \/ @i2@) — so one function covers whichever pair of
-- tensors an instance uses. This is the bifunctor analog of the covariant half
-- of "Data.Functor.Monoidal.Laws": the coherence squares are compared with 'Eq'
-- and re-association happens with 'bimap' over both tensor positions.
--
-- The rank-2 generator @forall a b. 'Gen' a -> 'Gen' b -> 'Gen' (f a b)@ lets a
-- law instantiate @f@ at the several element types the coherence square needs.
module Data.Bifunctor.Monoidal.Laws
  ( -- * Covariant bifunctors
    semigroupalLaws,
    unitalLaws,
    monoidalLaws,

    -- * Profunctors
    profunctorSemigroupalLaws,
    profunctorUnitalLaws,
    profunctorMonoidalLaws,
  )
where

--------------------------------------------------------------------------------

import Control.Category.Tensor (Associative (assoc), Iso (bwd, fwd), Tensor (unitl, unitr), gbimap)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Bifunctor.Monoidal (Monoidal, Semigroupal (combine), Unital (introduce))
import Data.Profunctor (Profunctor (dimap))
import Hedgehog (Gen, Property, forAll, forAllWith, property, (===))
import Hedgehog.Classes (Laws (..))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------

-- | The element type the coherence squares are witnessed at.
genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

--------------------------------------------------------------------------------

-- | 'combine' laws: it commutes with the codomain tensors' associators
-- (associativity) and with maps into them (naturality of the laxator).
semigroupalLaws ::
  forall t1 t2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Associative (->) t1,
    Associative (->) t2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b),
    forall a b. (Eq a, Eq b) => Eq (t2 a b),
    forall a b. (Show a, Show b) => Show (t2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
semigroupalLaws genF =
  Laws
    "Semigroupal"
    [ ("Associativity", semigroupalAssoc @t1 @t2 genF),
      ("Naturality", semigroupalNaturality @t1 @t2 genF)
    ]

semigroupalAssoc ::
  forall t1 t2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Associative (->) t1,
    Associative (->) t2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b),
    forall a b. (Eq a, Eq b) => Eq (t2 a b),
    forall a b. (Show a, Show b) => Show (t2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
semigroupalAssoc genF = property $ do
  x <- forAll (genF genInt genInt)
  y <- forAll (genF genInt genInt)
  z <- forAll (genF genInt genInt)
  bimap (bwd (assoc @(->) @t1)) (bwd (assoc @(->) @t2)) (combine @(->) @t1 @t2 @(,) (combine @(->) @t1 @t2 @(,) (x, y), z))
    === combine @(->) @t1 @t2 @(,) (x, combine @(->) @t1 @t2 @(,) (y, z))

semigroupalNaturality ::
  forall t1 t2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Associative (->) t1,
    Associative (->) t2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b),
    forall a b. (Eq a, Eq b) => Eq (t2 a b),
    forall a b. (Show a, Show b) => Show (t2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
semigroupalNaturality genF = property $ do
  x <- forAll (genF genInt genInt)
  y <- forAll (genF genInt genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  bimap (gbimap @(->) @(->) @(->) @t1 g g) (gbimap @(->) @(->) @(->) @t2 h h) (combine @(->) @t1 @t2 @(,) (x, y))
    === combine @(->) @t1 @t2 @(,) (bimap g h x, bimap g h y)

--------------------------------------------------------------------------------

-- | Left and right unit laws: 'introduce' is a unit for 'combine', up to the
-- codomain tensors' unitors.
unitalLaws ::
  forall t1 i1 t2 i2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Unital (->) i1 i2 () f,
    Tensor (->) t1 i1,
    Tensor (->) t2 i2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
unitalLaws genF =
  Laws
    "Unital"
    [ ("Left Unit", unitalLeft @t1 @i1 @t2 @i2 genF),
      ("Right Unit", unitalRight @t1 @i1 @t2 @i2 genF)
    ]

unitalLeft ::
  forall t1 i1 t2 i2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Unital (->) i1 i2 () f,
    Tensor (->) t1 i1,
    Tensor (->) t2 i2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
unitalLeft genF = property $ do
  fab <- forAll (genF genInt genInt)
  bimap (fwd (unitl @(->) @t1)) (fwd (unitl @(->) @t2)) (combine @(->) @t1 @t2 @(,) (introduce @(->) @i1 @i2 @() (), fab))
    === fab

unitalRight ::
  forall t1 i1 t2 i2 f.
  ( Semigroupal (->) t1 t2 (,) f,
    Unital (->) i1 i2 () f,
    Tensor (->) t1 i1,
    Tensor (->) t2 i2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
unitalRight genF = property $ do
  fab <- forAll (genF genInt genInt)
  bimap (fwd (unitr @(->) @t1)) (fwd (unitr @(->) @t2)) (combine @(->) @t1 @t2 @(,) (fab, introduce @(->) @i1 @i2 @() ()))
    === fab

--------------------------------------------------------------------------------

-- | Every 'semigroupalLaws' and 'unitalLaws' property together, for a full
-- covariant bifunctor 'Monoidal' instance.
monoidalLaws ::
  forall t1 i1 t2 i2 f.
  ( Monoidal (->) t1 i1 t2 i2 (,) () f,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (t1 a b),
    forall a b. (Show a, Show b) => Show (t1 a b),
    forall a b. (Eq a, Eq b) => Eq (t2 a b),
    forall a b. (Show a, Show b) => Show (t2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
monoidalLaws genF =
  Laws
    "Monoidal"
    ( lawsProperties (semigroupalLaws @t1 @t2 genF)
        <> lawsProperties (unitalLaws @t1 @i1 @t2 @i2 genF)
    )

--------------------------------------------------------------------------------
-- Profunctors
--
-- The function-like instances ('(->)', @'Data.Profunctor.Star' f@,
-- @'Control.Arrow.Kleisli' f@, …) are /profunctors/, not covariant bifunctors:
-- contravariant in the first argument, and with no 'Eq' \/ 'Show'. So the laws
-- re-associate with 'dimap' (@fwd@ on the contravariant side, @bwd@ on the
-- covariant side) and are observed extensionally through a caller-supplied
-- @run@, exactly as the contravariant-functor laws of
-- "Data.Functor.Monoidal.Laws" are. @genP@ generates (opaque) profunctor values
-- and @genT1@ builds the contravariant-side input tensor.

-- | 'combine' laws for a /profunctor/: associativity and naturality of the
-- laxator, observed through @run@.
profunctorSemigroupalLaws ::
  forall t1 t2 p obs.
  ( Semigroupal (->) t1 t2 (,) p,
    Profunctor p,
    Associative (->) t1,
    Associative (->) t2,
    Eq (obs (t2 Int (t2 Int Int))),
    Show (obs (t2 Int (t2 Int Int))),
    Eq (obs (t2 Int Int)),
    Show (obs (t2 Int Int)),
    Show (t1 Int (t1 Int Int)),
    Show (t1 Int Int)
  ) =>
  (forall a b. p a b -> a -> obs b) ->
  Gen (p Int Int) ->
  (forall x y. Gen x -> Gen y -> Gen (t1 x y)) ->
  Laws
profunctorSemigroupalLaws run genP genT1 =
  Laws
    "Semigroupal"
    [ ( "Associativity",
        property $ do
          x <- forAllWith (const "<opaque>") genP
          y <- forAllWith (const "<opaque>") genP
          z <- forAllWith (const "<opaque>") genP
          inp <- forAll (genT1 genInt (genT1 genInt genInt))
          run (dimap (fwd (assoc @(->) @t1)) (bwd (assoc @(->) @t2)) (combine @(->) @t1 @t2 @(,) (combine @(->) @t1 @t2 @(,) (x, y), z))) inp
            === run (combine @(->) @t1 @t2 @(,) (x, combine @(->) @t1 @t2 @(,) (y, z))) inp
      ),
      ( "Naturality",
        property $ do
          x <- forAllWith (const "<opaque>") genP
          y <- forAllWith (const "<opaque>") genP
          inp <- forAll (genT1 genInt genInt)
          let g = (+ 1) :: Int -> Int
              h = (* 2) :: Int -> Int
          run (dimap (gbimap @(->) @(->) @(->) @t1 g g) (gbimap @(->) @(->) @(->) @t2 h h) (combine @(->) @t1 @t2 @(,) (x, y))) inp
            === run (combine @(->) @t1 @t2 @(,) (dimap g h x, dimap g h y)) inp
      )
    ]

-- | Left and right unit laws for a /profunctor/, observed through @run@ on a
-- generated element.
profunctorUnitalLaws ::
  forall t1 i1 t2 i2 p obs.
  ( Semigroupal (->) t1 t2 (,) p,
    Unital (->) i1 i2 () p,
    Profunctor p,
    Tensor (->) t1 i1,
    Tensor (->) t2 i2,
    Eq (obs Int),
    Show (obs Int)
  ) =>
  (forall a b. p a b -> a -> obs b) ->
  Gen (p Int Int) ->
  Laws
profunctorUnitalLaws run genP =
  Laws
    "Unital"
    [ ( "Left Unit",
        property $ do
          pab <- forAllWith (const "<opaque>") genP
          inp <- forAll genInt
          run (dimap (bwd (unitl @(->) @t1)) (fwd (unitl @(->) @t2)) (combine @(->) @t1 @t2 @(,) (introduce @(->) @i1 @i2 @() (), pab))) inp
            === run pab inp
      ),
      ( "Right Unit",
        property $ do
          pab <- forAllWith (const "<opaque>") genP
          inp <- forAll genInt
          run (dimap (bwd (unitr @(->) @t1)) (fwd (unitr @(->) @t2)) (combine @(->) @t1 @t2 @(,) (pab, introduce @(->) @i1 @i2 @() ()))) inp
            === run pab inp
      )
    ]

-- | Every 'profunctorSemigroupalLaws' and 'profunctorUnitalLaws' property
-- together, for a full profunctor 'Monoidal' instance.
profunctorMonoidalLaws ::
  forall t1 i1 t2 i2 p obs.
  ( Monoidal (->) t1 i1 t2 i2 (,) () p,
    Profunctor p,
    Eq (obs (t2 Int (t2 Int Int))),
    Show (obs (t2 Int (t2 Int Int))),
    Eq (obs (t2 Int Int)),
    Show (obs (t2 Int Int)),
    Eq (obs Int),
    Show (obs Int),
    Show (t1 Int (t1 Int Int)),
    Show (t1 Int Int)
  ) =>
  (forall a b. p a b -> a -> obs b) ->
  Gen (p Int Int) ->
  (forall x y. Gen x -> Gen y -> Gen (t1 x y)) ->
  Laws
profunctorMonoidalLaws run genP genT1 =
  Laws
    "Monoidal"
    ( lawsProperties (profunctorSemigroupalLaws @t1 @t2 run genP genT1)
        <> lawsProperties (profunctorUnitalLaws @t1 @i1 @t2 @i2 run genP)
    )
