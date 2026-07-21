{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Category.Tensor (Associative (..), GBifunctor (..), Iso (..), Tensor (unitl, unitr))
import Control.Monad (unless)
import Data.Distributive (Distributive (..))
import Data.Functor.Contravariant (Contravariant (..), Op (..), Predicate (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Functor.Monoidal.Generic (FromGeneric (..), FromRepresentable (..))
import Data.Monoid (Sum (..))
import Data.These (These (..))
import Data.Void (Void)
import Generics.Kind.TH (deriveGenericK)
import Hedgehog (Gen, Group (..), Property, checkSequential, forAll, forAllWith, property, (===))
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import System.Exit (exitFailure)

--------------------------------------------------------------------------------
-- Test types, one per rep shape

-- | A nullary constructor. Exercises @U1@.
data Phantom a = Phantom deriving (Functor, Show, Eq)

$(deriveGenericK ''Phantom)

deriving via FromGeneric Phantom instance Semigroupal (->) (,) (,) Phantom

deriving via FromGeneric Phantom instance Unital (->) () () Phantom

deriving via FromGeneric Phantom instance Monoidal (->) (,) () (,) () Phantom

-- | Two bare parameters. Exercises @Field Var0@ and @:*:@, and is
-- representable, so it also gets the coherent split.
data Two a = Two a a deriving (Functor, Show, Eq)

$(deriveGenericK ''Two)

instance Distributive Two where
  distribute w = Two (fmap (\(Two a _) -> a) w) (fmap (\(Two _ b) -> b) w)

deriving via FromGeneric Two instance Semigroupal (->) (,) (,) Two

deriving via FromRepresentable Two instance Semigroupal Op (,) (,) Two

deriving via FromGeneric Two instance Unital (->) () () Two

deriving via FromGeneric Two instance Monoidal (->) (,) () (,) () Two

-- | Sub-functor fields. Exercises @Field (Kon g :@: Var0)@ across three tensors.
data P a = P (Maybe a) [a] deriving (Functor, Show, Eq)

$(deriveGenericK ''P)

deriving via FromGeneric P instance Semigroupal (->) (,) (,) P

deriving via FromGeneric P instance Semigroupal (->) Either (,) P

deriving via FromGeneric P instance Semigroupal (->) These (,) P

deriving via FromGeneric P instance Semigroupal Op (,) (,) P

deriving via FromGeneric P instance Unital (->) () () P

deriving via FromGeneric P instance Monoidal (->) (,) () (,) () P

deriving via FromGeneric P instance Unital (->) Void () P

deriving via FromGeneric P instance Monoidal (->) Either Void (,) () P

-- | A constant 'Monoid' field. Exercises @Field (Kon c)@.
data W a = W String (Maybe a) deriving (Functor, Show, Eq)

$(deriveGenericK ''W)

deriving via FromGeneric W instance Semigroupal (->) (,) (,) W

deriving via FromGeneric W instance Unital (->) () () W

deriving via FromGeneric W instance Monoidal (->) (,) () (,) () W

deriving via FromGeneric W instance Semigroupal (->) Either (,) W

deriving via FromGeneric W instance Unital (->) Void () W

deriving via FromGeneric W instance Monoidal (->) Either Void (,) () W

-- | A nested functor field. Exercises @Field (Kon f :@: (Kon g :@: Var0))@.
data Nest a = Nest (Maybe [a]) deriving (Functor, Show, Eq)

$(deriveGenericK ''Nest)

deriving via FromGeneric Nest instance Semigroupal (->) (,) (,) Nest

deriving via FromGeneric Nest instance Semigroupal Op (,) (,) Nest

deriving via FromGeneric Nest instance Unital (->) () () Nest

deriving via FromGeneric Nest instance Monoidal (->) (,) () (,) () Nest

deriving via FromGeneric Nest instance Semigroupal (->) Either (,) Nest

deriving via FromGeneric Nest instance Unital (->) Void () Nest

deriving via FromGeneric Nest instance Monoidal (->) Either Void (,) () Nest

-- | A record with named fields. Exercises the selector metadata.
data Rec a = Rec {recFst :: Maybe a, recSnd :: [a]} deriving (Functor, Show, Eq)

$(deriveGenericK ''Rec)

deriving via FromGeneric Rec instance Semigroupal (->) (,) (,) Rec

deriving via FromGeneric Rec instance Unital (->) () () Rec

deriving via FromGeneric Rec instance Monoidal (->) (,) () (,) () Rec

-- | A mixed three-field product. Exercises @Var0@, @Kon g :@: Var0@, and
-- @Kon c@ together.
data Mix a = Mix a (Maybe a) (Sum Int) deriving (Functor, Show, Eq)

$(deriveGenericK ''Mix)

deriving via FromGeneric Mix instance Semigroupal (->) (,) (,) Mix

deriving via FromGeneric Mix instance Unital (->) () () Mix

deriving via FromGeneric Mix instance Monoidal (->) (,) () (,) () Mix

-- | A sum of sub-functor fields. Combine is undefined, so it gets only the
-- (total) split.
data S a = SL (Maybe a) | SR [a] deriving (Functor, Show, Eq)

$(deriveGenericK ''S)

deriving via FromGeneric S instance Semigroupal Op (,) (,) S

-- | A three-constructor sum mixing bare parameters and a nullary constructor.
data Sum3 a = A a | B a a | C deriving (Functor, Show, Eq)

$(deriveGenericK ''Sum3)

deriving via FromGeneric Sum3 instance Semigroupal Op (,) (,) Sum3

-- | A contravariant functor. Exercises the @Divisible@ leaf.
data TwoPreds a = TwoPreds (Predicate a) (Predicate a)

$(deriveGenericK ''TwoPreds)

deriving via FromGeneric TwoPreds instance Semigroupal (->) (,) (,) TwoPreds

deriving via FromGeneric TwoPreds instance Unital (->) () () TwoPreds

deriving via FromGeneric TwoPreds instance Monoidal (->) (,) () (,) () TwoPreds

instance Contravariant TwoPreds where
  contramap f (TwoPreds p q) = TwoPreds (contramap f p) (contramap f q)

--------------------------------------------------------------------------------
-- Generators

genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

genPhantom :: Gen a -> Gen (Phantom a)
genPhantom _ = pure Phantom

genTwo :: Gen a -> Gen (Two a)
genTwo g = Two <$> g <*> g

genP :: Gen a -> Gen (P a)
genP g = P <$> Gen.maybe g <*> Gen.list (Range.linear 0 4) g

genW :: Gen a -> Gen (W a)
genW g = W <$> Gen.string (Range.linear 0 3) Gen.alpha <*> Gen.maybe g

genNest :: Gen a -> Gen (Nest a)
genNest g = Nest <$> Gen.maybe (Gen.list (Range.linear 0 3) g)

genRec :: Gen a -> Gen (Rec a)
genRec g = Rec <$> Gen.maybe g <*> Gen.list (Range.linear 0 4) g

genMix :: Gen a -> Gen (Mix a)
genMix g = Mix <$> g <*> Gen.maybe g <*> (Sum <$> genInt)

genS :: Gen a -> Gen (S a)
genS g = Gen.choice [SL <$> Gen.maybe g, SR <$> Gen.list (Range.linear 0 4) g]

genSum3 :: Gen a -> Gen (Sum3 a)
genSum3 g = Gen.choice [A <$> g, B <$> g <*> g, pure C]

genPair :: Gen a -> Gen (a, a)
genPair g = (,) <$> g <*> g

genTwoPreds :: Gen (TwoPreds Int)
genTwoPreds = TwoPreds <$> genPredInt <*> genPredInt
  where
    genPredInt = (\n -> Predicate (> n)) <$> genInt

--------------------------------------------------------------------------------
-- Property laws

-- | Semigroupal associativity, for any codomain tensor @t@. @combine@ commutes
-- with the tensor's associator.
generalAssoc ::
  forall t f.
  ( Semigroupal (->) t (,) f,
    Associative (->) t,
    Functor f,
    forall a. (Eq a) => Eq (f a),
    forall a. (Show a) => Show (f a),
    forall a b. (Eq a, Eq b) => Eq (t a b),
    forall a b. (Show a, Show b) => Show (t a b)
  ) =>
  (forall a. Gen a -> Gen (f a)) ->
  Property
generalAssoc genF = property $ do
  x <- forAll (genF genInt)
  y <- forAll (genF genInt)
  z <- forAll (genF genInt)
  fmap (bwd (assoc @(->) @t)) (combine @(->) @t @(,) (combine @(->) @t @(,) (x, y), z))
    === combine @(->) @t @(,) (x, combine @(->) @t @(,) (y, z))

-- | Naturality of @combine@ in both arguments, for any codomain tensor. This is
-- a free theorem, so it is checked as a guard against machinery bugs.
naturalityLaw ::
  forall t f.
  ( Semigroupal (->) t (,) f,
    Associative (->) t,
    Functor f,
    forall a. (Eq a) => Eq (f a),
    forall a. (Show a) => Show (f a),
    forall a b. (Eq a, Eq b) => Eq (t a b),
    forall a b. (Show a, Show b) => Show (t a b)
  ) =>
  (forall a. Gen a -> Gen (f a)) ->
  Property
naturalityLaw genF = property $ do
  x <- forAll (genF genInt)
  y <- forAll (genF genInt)
  let g = (+ 1) :: Int -> Int
      h = (* 2) :: Int -> Int
  fmap (gbimap @(->) @(->) @(->) @t g h) (combine @(->) @t @(,) (x, y))
    === combine @(->) @t @(,) (fmap g x, fmap h y)

-- | The Monoidal left and right unit laws, for any codomain tensor @t1@ paired
-- with its unit @i1@. @combine@ against the derived unit, followed by the
-- tensor's unitor, is the identity.
unitLaw ::
  forall t1 i1 f.
  ( Monoidal (->) t1 i1 (,) () f,
    Tensor (->) t1 i1,
    Functor f,
    forall a. (Eq a) => Eq (f a),
    forall a. (Show a) => Show (f a)
  ) =>
  (forall a. Gen a -> Gen (f a)) ->
  Property
unitLaw genF = property $ do
  fa <- forAll (genF genInt)
  fmap (fwd (unitl @(->) @t1)) (combine @(->) @t1 @(,) (introduce @(->) @i1 @() (), fa)) === fa
  fmap (fwd (unitr @(->) @t1)) (combine @(->) @t1 @(,) (fa, introduce @(->) @i1 @() ())) === fa

-- | The contravariant unit laws for 'TwoPreds', observed extensionally. For a
-- contravariant functor the unitor is applied through 'contramap' in the
-- opposite direction.
contraUnit :: Property
contraUnit = property $ do
  x <- forAllWith (const "<opaque>") genTwoPreds
  a <- forAll genInt
  let l = contramap (bwd (unitl @(->) @(,))) (combine @(->) @(,) @(,) (introduce @(->) @() @() (), x))
      r = contramap (bwd (unitr @(->) @(,))) (combine @(->) @(,) @(,) (x, introduce @(->) @() @() ()))
  obsTwoPreds l a === obsTwoPreds x a
  obsTwoPreds r a === obsTwoPreds x a

-- | The standalone split is the functorial unzip.
splitLaw ::
  forall f.
  ( Semigroupal Op (,) (,) f,
    Functor f,
    forall a. (Eq a) => Eq (f a),
    forall a. (Show a) => Show (f a)
  ) =>
  (forall a. Gen a -> Gen (f a)) ->
  Property
splitLaw genF = property $ do
  s <- forAll (genF (genPair genInt))
  getOp (combine @Op @(,) @(,)) s === (fmap fst s, fmap snd s)

-- | The derived combine agrees with the field-wise applicative combine.
referenceP :: Property
referenceP = property $ do
  P ma la <- forAll (genP genInt)
  P mb lb <- forAll (genP genInt)
  combine @(->) @(,) @(,) (P ma la, P mb lb)
    === P (liftA2 (,) ma mb) (liftA2 (,) la lb)

-- | For a representable functor the split inverts combine and vice versa.
coherenceTwo :: Property
coherenceTwo = property $ do
  x <- forAll (genTwo genInt)
  y <- forAll (genTwo genInt)
  xy <- forAll (genTwo (genPair genInt))
  getOp (combine @Op @(,) @(,)) (combine @(->) @(,) @(,) (x, y)) === (x, y)
  combine @(->) @(,) @(,) (getOp (combine @Op @(,) @(,)) xy) === xy

-- | The contravariant combine divides its input across the two predicates.
contravariantTwoPreds :: Property
contravariantTwoPreds = property $ do
  n1 <- forAll genInt
  n2 <- forAll genInt
  n3 <- forAll genInt
  n4 <- forAll genInt
  let TwoPreds f g =
        combine @(->) @(,) @(,)
          ( TwoPreds (Predicate (> n1)) (Predicate (> n2)),
            TwoPreds (Predicate (> n3)) (Predicate (> n4))
          )
  a <- forAll genInt
  b <- forAll genInt
  getPredicate f (a, b) === (a > n1 && b > n3)
  getPredicate g (a, b) === (a > n2 && b > n4)

-- | Contravariant associativity. @combine@ commutes with the associator via
-- 'contramap', checked extensionally by observing on a generated input.
contraAssoc ::
  forall f r.
  (Semigroupal (->) (,) (,) f, Contravariant f, Eq r, Show r) =>
  Gen (f Int) ->
  (forall a. f a -> a -> r) ->
  Property
contraAssoc genFInt obs = property $ do
  x <- forAllWith (const "<opaque>") genFInt
  y <- forAllWith (const "<opaque>") genFInt
  z <- forAllWith (const "<opaque>") genFInt
  i <- forAll ((,) <$> genInt <*> genPair genInt)
  let lhs = contramap (fwd (assoc @(->) @(,))) (combine @(->) @(,) @(,) (combine @(->) @(,) @(,) (x, y), z))
      rhs = combine @(->) @(,) @(,) (x, combine @(->) @(,) @(,) (y, z))
  obs lhs i === obs rhs i

obsTwoPreds :: TwoPreds a -> a -> (Bool, Bool)
obsTwoPreds (TwoPreds p q) a = (getPredicate p a, getPredicate q a)

--------------------------------------------------------------------------------
-- Concrete checks for the tensors the property laws do not cover

check :: (Eq a, Show a) => String -> a -> a -> IO Bool
check name got want
  | got == want = putStrLn ("ok   " ++ name) >> pure True
  | otherwise = putStrLn ("FAIL " ++ name ++ ": got " ++ show got ++ ", want " ++ show want) >> pure False

main :: IO ()
main = do
  u1 <-
    check
      "P (Either tensor)"
      (combine @(->) @Either @(,) (P (Just 1) [1, 2], P (Just 3) [4]))
      (P (Just (Left 1)) [Left 1, Left 2, Right 4] :: P (Either Int Int))
  u2 <-
    check
      "P (These tensor)"
      (combine @(->) @These @(,) (P (Just 1) [1, 2], P (Just 3) [4]))
      (P (Just (These 1 3)) [These 1 4, This 2] :: P (These Int Int))
  u3 <-
    check
      "Nest (nested combine)"
      (combine @(->) @(,) @(,) (Nest (Just [1, 2]), Nest (Just [3, 4])))
      (Nest (Just [(1, 3), (1, 4), (2, 3), (2, 4)]) :: Nest (Int, Int))
  u4 <-
    check
      "P (introduce unit)"
      (introduce @(->) @() @() () :: P ())
      (P (Just ()) [()])
  u5 <-
    check
      "P (introduce Void unit)"
      (introduce @(->) @Void @() () :: P Void)
      (P Nothing [])
  props <-
    checkSequential $
      Group
        "generic-deriving laws"
        [ ("assoc (,) Phantom", generalAssoc @(,) genPhantom),
          ("assoc (,) Two", generalAssoc @(,) genTwo),
          ("assoc (,) P", generalAssoc @(,) genP),
          ("assoc (,) W", generalAssoc @(,) genW),
          ("assoc (,) Nest", generalAssoc @(,) genNest),
          ("assoc (,) Rec", generalAssoc @(,) genRec),
          ("assoc (,) Mix", generalAssoc @(,) genMix),
          ("assoc Either P", generalAssoc @Either genP),
          ("assoc These P", generalAssoc @These genP),
          ("naturality (,) P", naturalityLaw @(,) genP),
          ("naturality Either P", naturalityLaw @Either genP),
          ("naturality These P", naturalityLaw @These genP),
          ("unit (,) Phantom", unitLaw @(,) @() genPhantom),
          ("unit (,) Two", unitLaw @(,) @() genTwo),
          ("unit (,) P", unitLaw @(,) @() genP),
          ("unit (,) W", unitLaw @(,) @() genW),
          ("unit (,) Nest", unitLaw @(,) @() genNest),
          ("unit (,) Rec", unitLaw @(,) @() genRec),
          ("unit (,) Mix", unitLaw @(,) @() genMix),
          ("unit Either P", unitLaw @Either @Void genP),
          ("unit Either W", unitLaw @Either @Void genW),
          ("unit Either Nest", unitLaw @Either @Void genNest),
          ("contravariant unit TwoPreds", contraUnit),
          ("split unzip P", splitLaw @P genP),
          ("split unzip Nest", splitLaw @Nest genNest),
          ("split unzip S", splitLaw @S genS),
          ("split unzip Sum3", splitLaw @Sum3 genSum3),
          ("reference P", referenceP),
          ("representable coherence Two", coherenceTwo),
          ("contravariant divide TwoPreds", contravariantTwoPreds),
          ("contravariant assoc TwoPreds", contraAssoc genTwoPreds obsTwoPreds)
        ]
  unless (and [u1, u2, u3, u4, u5] && props) exitFailure
