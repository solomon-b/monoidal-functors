{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
-- kindly-functors does not yet cover Kleisli at the profunctor arity, so we
-- fill in the two missing instances locally.
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Exercises the generically derived rank-2 'Rank2.Traversable' for
-- profunctor-interpreted HKDs. Sequencing a record of @p a b@ fields yields
-- @p (hkd 'Rank2.First') (hkd 'Rank2.Second')@, which must act field-wise.
module Data.Bifunctor.Rank2.TraversableSpec (tests) where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Control.Category.LawsSupport (genInt)
import Data.Bifunctor.Rank2.Traversable qualified as Rank2
import Data.Functor.Contravariant (Op (..))
import Data.Kind (Type)
import GHC.Generics (Generic)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, property, withTests, (===))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kindly (CategoricalFunctor (..), FunctorOf, MapArg2, Nat (..), type (~>))
import Prelude

--------------------------------------------------------------------------------
-- Orphan kindly-functors instances for Kleisli at the profunctor arity

instance (FunctorOf (->) (->) m) => CategoricalFunctor (Kleisli m) where
  type Dom (Kleisli m) = Op
  type Cod (Kleisli m) = (->) ~> (->)

  map :: Op a a' -> ((->) ~> (->)) (Kleisli m a) (Kleisli m a')
  map (Op f) = Nat (\(Kleisli g) -> Kleisli (g . f))

instance (FunctorOf (->) (->) m) => MapArg2 Op (->) (Kleisli m)

--------------------------------------------------------------------------------
-- Test types

-- | A three-field record of profunctor values. Exercises @K1@, @M1@, and
-- nested @:*:@.
data TestHKD p = TestHKD
  { thFun :: p Int Bool,
    thLen :: p String Int,
    thFlag :: p Bool String
  }
  deriving stock (Generic)
  deriving anyclass (Rank2.Traversable)

deriving stock instance (Show (p Int Bool), Show (p String Int), Show (p Bool String)) => Show (TestHKD p)

deriving stock instance (Eq (p Int Bool), Eq (p String Int), Eq (p Bool String)) => Eq (TestHKD p)

-- | A nullary constructor. Exercises @U1@ and the 'introduce' path.
data EmptyHKD (p :: Type -> Type -> Type) = EmptyHKD
  deriving stock (Generic, Show, Eq)
  deriving anyclass (Rank2.Traversable)

--------------------------------------------------------------------------------
-- Generators

genString :: Gen String
genString = Gen.string (Range.linear 0 5) Gen.alpha

--------------------------------------------------------------------------------
-- Properties

-- | Sequencing a record of functions gives a function between records that
-- applies each field pointwise.
functionActsFieldwise :: Property
functionActsFieldwise = property $ do
  k <- forAll genInt
  m <- forAll genInt
  let hkd = TestHKD {thFun = \n -> n > k, thLen = \s -> length s + m, thFlag = \b -> if b then show k else show m}
      run = Rank2.sequence hkd
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  run (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === TestHKD (Rank2.Second (a > k)) (Rank2.Second (length s + m)) (Rank2.Second (if b then show k else show m))

-- | Sequencing a record of 'Kleisli' arrows combines the effects field-wise,
-- agreeing with the applicative reference.
kleisliAgrees :: Property
kleisliAgrees = property $ do
  k <- forAll genInt
  m <- forAll genInt
  let f n = if n > k then Just (even n) else Nothing
      g s = if length s > m then Just (length s) else Nothing
      h b = if b then Just (show k) else Nothing
      hkd = TestHKD (Kleisli f) (Kleisli g) (Kleisli h)
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  runKleisli (Rank2.sequence hkd) (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === ((\x y z -> TestHKD (Rank2.Second x) (Rank2.Second y) (Rank2.Second z)) <$> f a <*> g s <*> h b)

-- | At @Kleisli []@ the effect order is observable: 'Maybe' cannot tell a
-- flipped combine apart, but the cartesian product of multi-element lists
-- pins the left-to-right ordering against the applicative reference.
kleisliOrdersEffects :: Property
kleisliOrdersEffects = property $ do
  k <- forAll genInt
  let f n = [even n, n > k]
      g s = [length s, length s + k]
      h b = [show b, show (b, k)]
      hkd = TestHKD (Kleisli f) (Kleisli g) (Kleisli h)
  a <- forAll genInt
  s <- forAll genString
  b <- forAll Gen.bool
  runKleisli (Rank2.sequence hkd) (TestHKD (Rank2.First a) (Rank2.First s) (Rank2.First b))
    === ((\x y z -> TestHKD (Rank2.Second x) (Rank2.Second y) (Rank2.Second z)) <$> f a <*> g s <*> h b)

-- | A field-less record sequences to the unit of the profunctor via
-- 'introduce'.
emptySequencesToUnit :: Property
emptySequencesToUnit = withTests 1 $ property $ do
  Rank2.sequence (EmptyHKD :: EmptyHKD (->)) EmptyHKD === EmptyHKD
  runKleisli (Rank2.sequence (EmptyHKD :: EmptyHKD (Kleisli Maybe))) EmptyHKD === Just EmptyHKD

--------------------------------------------------------------------------------

tests :: IO Bool
tests =
  checkSequential $
    Group
      "Data.Bifunctor.Rank2.Traversable"
      [ ("function sequencing acts field-wise", functionActsFieldwise),
        ("Kleisli sequencing agrees with reference", kleisliAgrees),
        ("Kleisli sequencing orders effects left-to-right", kleisliOrdersEffects),
        ("empty record sequences to unit", emptySequencesToUnit)
      ]
