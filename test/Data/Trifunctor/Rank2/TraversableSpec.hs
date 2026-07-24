{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | Exercises the generically derived rank-2 'Rank2.Traversable' for
-- trifunctor-interpreted HKDs. No monoidal trifunctor instances ship with the
-- library yet, so the spec defines 'Shear', a minimal inhabitant of
-- @'Kindly.Trifunctor' (->) 'Op' (->)@ that is monoidal with respect to
-- tupling. Sequencing a record of @p a b c@ fields yields
-- @p (hkd 'Rank2.First') (hkd 'Rank2.Second') (hkd 'Rank2.Third')@, which
-- must act field-wise.
module Data.Trifunctor.Rank2.TraversableSpec (tests) where

--------------------------------------------------------------------------------

import Control.Category.LawsSupport (genInt)
import Data.Functor.Contravariant (Op (..))
import Data.Kind (Type)
import Data.Trifunctor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Trifunctor.Rank2.Traversable qualified as Rank2
import GHC.Generics (Generic)
import Hedgehog (Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Kindly (CategoricalFunctor (..), MapArg1, MapArg2, MapArg3, Nat (..), type (~>))
import Prelude

--------------------------------------------------------------------------------

-- | The minimal trifunctor of variance @(covariant, contravariant, covariant)@
-- that is monoidal with respect to tupling: consume a @b@, produce an @a@ and
-- a @c@.
type Shear :: Type -> Type -> Type -> Type
newtype Shear a b c = Shear {runShear :: b -> (a, c)}

instance Functor (Shear a b) where
  fmap :: (c -> c') -> Shear a b c -> Shear a b c'
  fmap f (Shear g) = Shear (fmap f . g)

instance CategoricalFunctor (Shear a b) where
  type Dom (Shear a b) = (->)
  type Cod (Shear a b) = (->)

  map :: (c -> c') -> Shear a b c -> Shear a b c'
  map = fmap

instance MapArg1 (->) (Shear a b)

instance CategoricalFunctor (Shear a) where
  type Dom (Shear a) = Op
  type Cod (Shear a) = (->) ~> (->)

  map :: Op b b' -> ((->) ~> (->)) (Shear a b) (Shear a b')
  map (Op f) = Nat (\(Shear g) -> Shear (g . f))

instance MapArg2 Op (->) (Shear a)

instance CategoricalFunctor Shear where
  type Dom Shear = (->)
  type Cod Shear = Op ~> (->) ~> (->)

  map :: (a -> a') -> (Op ~> (->) ~> (->)) (Shear a) (Shear a')
  map f = Nat (Nat (\(Shear g) -> Shear (\b -> let (x, c) = g b in (f x, c))))

instance MapArg3 (->) Op (->) Shear

instance Semigroupal (->) (,) (,) (,) (,) Shear where
  combine :: (Shear x y z, Shear x' y' z') -> Shear (x, x') (y, y') (z, z')
  combine (Shear f, Shear g) = Shear $ \(y, y') ->
    let (x, z) = f y
        (x', z') = g y'
     in ((x, x'), (z, z'))

instance Unital (->) () () () () Shear where
  introduce :: () -> Shear () () ()
  introduce () = Shear (\() -> ((), ()))

instance Monoidal (->) (,) () (,) () (,) () (,) () Shear

--------------------------------------------------------------------------------
-- Test types

-- | A three-field record of trifunctor values. Exercises @K1@, @M1@, and
-- nested @:*:@.
data TestHKD p = TestHKD
  { thOne :: p Int Bool Char,
    thTwo :: p String Int Bool,
    thThree :: p Bool Char Int
  }
  deriving stock (Generic)
  deriving anyclass (Rank2.Traversable)

deriving stock instance (Show (p Int Bool Char), Show (p String Int Bool), Show (p Bool Char Int)) => Show (TestHKD p)

deriving stock instance (Eq (p Int Bool Char), Eq (p String Int Bool), Eq (p Bool Char Int)) => Eq (TestHKD p)

-- | A nullary constructor. Exercises @U1@ and the 'introduce' path.
data EmptyHKD (p :: Type -> Type -> Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)
  deriving anyclass (Rank2.Traversable)

--------------------------------------------------------------------------------
-- Properties

-- | Sequencing a record of shears gives a shear between records that applies
-- each field pointwise, splitting the 'Rank2.Second' inputs into
-- 'Rank2.First' and 'Rank2.Third' outputs.
shearActsFieldwise :: Property
shearActsFieldwise = property $ do
  n <- forAll genInt
  m <- forAll genInt
  let f b = (n + fromEnum b, if b then 'T' else 'F')
      g i = (show (i + m), even i)
      h c = (c > 'j', fromEnum c + m)
      hkd = TestHKD (Shear f) (Shear g) (Shear h)
  b <- forAll Gen.bool
  i <- forAll genInt
  c <- forAll Gen.alpha
  let (firsts, thirds) = runShear (Rank2.sequence hkd) (TestHKD (Rank2.Second b) (Rank2.Second i) (Rank2.Second c))
  firsts === TestHKD (Rank2.First (fst (f b))) (Rank2.First (fst (g i))) (Rank2.First (fst (h c)))
  thirds === TestHKD (Rank2.Third (snd (f b))) (Rank2.Third (snd (g i))) (Rank2.Third (snd (h c)))

-- | A field-less record sequences to the unit shear via 'introduce'.
emptySequencesToUnit :: Property
emptySequencesToUnit = withTests 1 $ property $ do
  runShear (Rank2.sequence (EmptyHKD :: EmptyHKD Shear)) EmptyHKD === (EmptyHKD, EmptyHKD)

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Trifunctor.Rank2.Traversable"
      [ ("shear sequencing acts field-wise", shearActsFieldwise),
        ("empty record sequences to unit", emptySequencesToUnit)
      ]
