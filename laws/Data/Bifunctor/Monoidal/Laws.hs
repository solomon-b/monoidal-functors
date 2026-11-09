{-# LANGUAGE AllowAmbiguousTypes #-}

-- | Reusable @hedgehog-classes@ 'Laws' for the /covariant/ bifunctor
-- 'Semigroupal' \/ 'Unital' \/ 'Monoidal' classes of
-- "Data.Bifunctor.Monoidal". A consumer can law-test their own instances the
-- same way they test 'Monoid' or 'Applicative'.
--
-- > import Data.Bifunctor.Monoidal.Laws (monoidalLaws)
-- > import Hedgehog.Classes (lawsCheck)
-- >
-- > main :: IO Bool
-- > main = lawsCheck (monoidalLaws @(,) @() @(,) @() genMyBifunctor)
--
-- Each law is stated at category @('->')@ over the /product/ codomain tensor
-- @(,)@, general in the two domain tensors @tC1@ \/ @tC2@ (and, for the unit
-- laws, their units @iC1@ \/ @iC2@). One function covers whichever pair of
-- tensors an instance uses. This is the bifunctor analog of the covariant half
-- of "Data.Functor.Monoidal.Laws". The coherence squares are compared with 'Eq'
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

    -- * Colax (Op) bifunctors
    opSemigroupalLaws,
  )
where

--------------------------------------------------------------------------------

import Control.Category.Tensor (Associative (assoc), Iso (bwd, fwd), Tensor (unitl, unitr), gbimap, glmap, grmap)
import Data.Bifunctor (Bifunctor (bimap))
import Data.Bifunctor.Monoidal (Monoidal, Semigroupal (combine), Unital (introduce))
import Data.Functor.Contravariant (Op (..))
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

-- | 'combine' laws. It commutes with the codomain tensors' associators
-- (associativity) and with maps into them (naturality of the laxator).
semigroupalLaws ::
  forall tC1 tC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Associative (->) tC1,
    Associative (->) tC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Eq a, Eq b) => Eq (tC2 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
semigroupalLaws genF =
  Laws
    "Semigroupal"
    [ ("Associativity", semigroupalAssoc @tC1 @tC2 genF),
      ("Naturality", semigroupalNaturality @tC1 @tC2 genF)
    ]

semigroupalAssoc ::
  forall tC1 tC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Associative (->) tC1,
    Associative (->) tC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Eq a, Eq b) => Eq (tC2 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
semigroupalAssoc genF = property $ do
  x <- forAll (genF genInt genInt)
  y <- forAll (genF genInt genInt)
  z <- forAll (genF genInt genInt)
  bimap (bwd (assoc @(->) @tC1)) (bwd (assoc @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (combine @(->) @tC1 @tC2 @(,) (x, y), z))
    === combine @(->) @tC1 @tC2 @(,) (x, combine @(->) @tC1 @tC2 @(,) (y, z))

semigroupalNaturality ::
  forall tC1 tC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Associative (->) tC1,
    Associative (->) tC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Eq a, Eq b) => Eq (tC2 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
semigroupalNaturality genF = property $ do
  x <- forAll (genF genInt genInt)
  y <- forAll (genF genInt genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  bimap (gbimap @(->) @(->) @(->) @tC1 g g) (gbimap @(->) @(->) @(->) @tC2 h h) (combine @(->) @tC1 @tC2 @(,) (x, y))
    === combine @(->) @tC1 @tC2 @(,) (bimap g h x, bimap g h y)

--------------------------------------------------------------------------------

-- | Left and right unit laws: 'introduce' is a unit for 'combine', up to the
-- codomain tensors' unitors.
unitalLaws ::
  forall tC1 iC1 tC2 iC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Unital (->) iC1 iC2 () f,
    Tensor (->) tC1 iC1,
    Tensor (->) tC2 iC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
unitalLaws genF =
  Laws
    "Unital"
    [ ("Left Unit", unitalLeft @tC1 @iC1 @tC2 @iC2 genF),
      ("Right Unit", unitalRight @tC1 @iC1 @tC2 @iC2 genF)
    ]

unitalLeft ::
  forall tC1 iC1 tC2 iC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Unital (->) iC1 iC2 () f,
    Tensor (->) tC1 iC1,
    Tensor (->) tC2 iC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
unitalLeft genF = property $ do
  fab <- forAll (genF genInt genInt)
  bimap (fwd (unitl @(->) @tC1)) (fwd (unitl @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (introduce @(->) @iC1 @iC2 @() (), fab))
    === fab

unitalRight ::
  forall tC1 iC1 tC2 iC2 f.
  ( Semigroupal (->) tC1 tC2 (,) f,
    Unital (->) iC1 iC2 () f,
    Tensor (->) tC1 iC1,
    Tensor (->) tC2 iC2,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Property
unitalRight genF = property $ do
  fab <- forAll (genF genInt genInt)
  bimap (fwd (unitr @(->) @tC1)) (fwd (unitr @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (fab, introduce @(->) @iC1 @iC2 @() ()))
    === fab

--------------------------------------------------------------------------------

-- | Every 'semigroupalLaws' and 'unitalLaws' property together, for a full
-- covariant bifunctor 'Monoidal' instance.
monoidalLaws ::
  forall tC1 iC1 tC2 iC2 f.
  ( Monoidal (->) tC1 iC1 tC2 iC2 (,) () f,
    Bifunctor f,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Eq a, Eq b) => Eq (tC2 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  Laws
monoidalLaws genF =
  Laws
    "Monoidal"
    ( lawsProperties (semigroupalLaws @tC1 @tC2 genF)
        <> lawsProperties (unitalLaws @tC1 @iC1 @tC2 @iC2 genF)
    )

--------------------------------------------------------------------------------
-- Colax (Op) bifunctors

-- | 'combine' laws for the colax (@'Op'@) direction. The split
-- @f (tC1 x x') (tC2 y y') -> tD (f x y) (f x' y')@ is coassociative and natural,
-- general in all three tensors. Covariant bifunctors compared with 'Eq'.
opSemigroupalLaws ::
  forall tC1 tC2 tD f.
  ( Semigroupal Op tC1 tC2 tD f,
    Associative (->) tC1,
    Associative (->) tC2,
    Associative (->) tD,
    Bifunctor f,
    Bifunctor tC1,
    Bifunctor tC2,
    Bifunctor tD,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC1 a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC2 a b)) ->
  Laws
opSemigroupalLaws genF genT1 genT2 =
  Laws
    "Semigroupal (Op)"
    [ ("Coassociativity", opCoassoc @tC1 @tC2 @tD genF genT1 genT2),
      ("Conaturality", opConaturality @tC1 @tC2 @tD genF genT1 genT2)
    ]

opCoassoc ::
  forall tC1 tC2 tD f.
  ( Semigroupal Op tC1 tC2 tD f,
    Associative (->) tC1,
    Associative (->) tC2,
    Associative (->) tD,
    Bifunctor f,
    Bifunctor tC1,
    Bifunctor tC2,
    Bifunctor tD,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC1 a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC2 a b)) ->
  Property
opCoassoc genF genT1 genT2 = property $ do
  w <- forAll (genF (genT1 genInt (genT1 genInt genInt)) (genT2 genInt (genT2 genInt genInt)))
  let split :: forall x x' y y'. f (tC1 x x') (tC2 y y') -> tD (f x y) (f x' y')
      split = getOp (combine @Op @tC1 @tC2 @tD)
      lhs = grmap @(->) @(->) @(->) @tD split (split w)
      rhs =
        bwd (assoc @(->) @tD) $
          glmap @(->) @(->) @(->) @tD split (split (bimap (fwd (assoc @(->) @tC1)) (fwd (assoc @(->) @tC2)) w))
  lhs === rhs

opConaturality ::
  forall tC1 tC2 tD f.
  ( Semigroupal Op tC1 tC2 tD f,
    Associative (->) tC1,
    Associative (->) tC2,
    Associative (->) tD,
    Bifunctor f,
    Bifunctor tC1,
    Bifunctor tC2,
    Bifunctor tD,
    forall a b. (Eq a, Eq b) => Eq (f a b),
    forall a b. (Show a, Show b) => Show (f a b),
    forall a b. (Eq a, Eq b) => Eq (tD a b),
    forall a b. (Show a, Show b) => Show (tD a b),
    forall a b. (Show a, Show b) => Show (tC1 a b),
    forall a b. (Show a, Show b) => Show (tC2 a b)
  ) =>
  (forall a b. Gen a -> Gen b -> Gen (f a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC1 a b)) ->
  (forall a b. Gen a -> Gen b -> Gen (tC2 a b)) ->
  Property
opConaturality genF genT1 genT2 = property $ do
  w <- forAll (genF (genT1 genInt genInt) (genT2 genInt genInt))
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
      split :: forall x x' y y'. f (tC1 x x') (tC2 y y') -> tD (f x y) (f x' y')
      split = getOp (combine @Op @tC1 @tC2 @tD)
  split (bimap (gbimap @(->) @(->) @(->) @tC1 g g) (gbimap @(->) @(->) @(->) @tC2 h h) w)
    === gbimap @(->) @(->) @(->) @tD (bimap g h) (bimap g h) (split w)

--------------------------------------------------------------------------------
-- Profunctors
--
-- The function-like instances ('(->)', @'Data.Profunctor.Star' f@,
-- @'Control.Arrow.Kleisli' f@, ...) are /profunctors/, not covariant bifunctors.
-- They are contravariant in the first argument, and have no 'Eq' \/ 'Show'. The laws
-- re-associate with 'dimap' (@fwd@ on the contravariant side, @bwd@ on the
-- covariant side) and are observed extensionally through a caller-supplied
-- @run@, as the contravariant-functor laws of
-- "Data.Functor.Monoidal.Laws" are. @genP@ generates (opaque) profunctor values
-- and @genT1@ builds the contravariant-side input tensor.

-- | 'combine' laws for a /profunctor/. Associativity and naturality of the
-- laxator, observed through @run@.
profunctorSemigroupalLaws ::
  forall tC1 tC2 p obs.
  ( Semigroupal (->) tC1 tC2 (,) p,
    Profunctor p,
    Associative (->) tC1,
    Associative (->) tC2,
    Eq (obs (tC2 Int (tC2 Int Int))),
    Show (obs (tC2 Int (tC2 Int Int))),
    Eq (obs (tC2 Int Int)),
    Show (obs (tC2 Int Int)),
    Show (tC1 Int (tC1 Int Int)),
    Show (tC1 Int Int)
  ) =>
  (forall a b. p a b -> a -> obs b) ->
  Gen (p Int Int) ->
  (forall x y. Gen x -> Gen y -> Gen (tC1 x y)) ->
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
          run (dimap (fwd (assoc @(->) @tC1)) (bwd (assoc @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (combine @(->) @tC1 @tC2 @(,) (x, y), z))) inp
            === run (combine @(->) @tC1 @tC2 @(,) (x, combine @(->) @tC1 @tC2 @(,) (y, z))) inp
      ),
      ( "Naturality",
        property $ do
          x <- forAllWith (const "<opaque>") genP
          y <- forAllWith (const "<opaque>") genP
          inp <- forAll (genT1 genInt genInt)
          let g = (+ 1) :: Int -> Int
              h = (* 2) :: Int -> Int
          run (dimap (gbimap @(->) @(->) @(->) @tC1 g g) (gbimap @(->) @(->) @(->) @tC2 h h) (combine @(->) @tC1 @tC2 @(,) (x, y))) inp
            === run (combine @(->) @tC1 @tC2 @(,) (dimap g h x, dimap g h y)) inp
      )
    ]

-- | Left and right unit laws for a /profunctor/, observed through @run@ on a
-- generated element.
profunctorUnitalLaws ::
  forall tC1 iC1 tC2 iC2 p obs.
  ( Semigroupal (->) tC1 tC2 (,) p,
    Unital (->) iC1 iC2 () p,
    Profunctor p,
    Tensor (->) tC1 iC1,
    Tensor (->) tC2 iC2,
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
          run (dimap (bwd (unitl @(->) @tC1)) (fwd (unitl @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (introduce @(->) @iC1 @iC2 @() (), pab))) inp
            === run pab inp
      ),
      ( "Right Unit",
        property $ do
          pab <- forAllWith (const "<opaque>") genP
          inp <- forAll genInt
          run (dimap (bwd (unitr @(->) @tC1)) (fwd (unitr @(->) @tC2)) (combine @(->) @tC1 @tC2 @(,) (pab, introduce @(->) @iC1 @iC2 @() ()))) inp
            === run pab inp
      )
    ]

-- | Every 'profunctorSemigroupalLaws' and 'profunctorUnitalLaws' property
-- together, for a full profunctor 'Monoidal' instance.
profunctorMonoidalLaws ::
  forall tC1 iC1 tC2 iC2 p obs.
  ( Monoidal (->) tC1 iC1 tC2 iC2 (,) () p,
    Profunctor p,
    Eq (obs (tC2 Int (tC2 Int Int))),
    Show (obs (tC2 Int (tC2 Int Int))),
    Eq (obs (tC2 Int Int)),
    Show (obs (tC2 Int Int)),
    Eq (obs Int),
    Show (obs Int),
    Show (tC1 Int (tC1 Int Int)),
    Show (tC1 Int Int)
  ) =>
  (forall a b. p a b -> a -> obs b) ->
  Gen (p Int Int) ->
  (forall x y. Gen x -> Gen y -> Gen (tC1 x y)) ->
  Laws
profunctorMonoidalLaws run genP genT1 =
  Laws
    "Monoidal"
    ( lawsProperties (profunctorSemigroupalLaws @tC1 @tC2 run genP genT1)
        <> lawsProperties (profunctorUnitalLaws @tC1 @iC1 @tC2 @iC2 run genP)
    )
