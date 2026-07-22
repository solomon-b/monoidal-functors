{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Functor.Monoidal.GenericSpec (tests) where

--------------------------------------------------------------------------------

import Control.Applicative (liftA2)
import Data.Distributive (Distributive (..))
import Data.Functor.Contravariant (Contravariant (..), Op (..), Predicate (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Functor.Monoidal.Generic (FromGeneric (..), FromRepresentable (..))
import Data.Functor.Monoidal.Laws
  ( contravariantMonoidalLaws,
    monoidalLaws,
    opSemigroupalLaws,
    representableSplitLaws,
    semigroupalLaws,
  )
import Data.Monoid (Sum (..))
import Data.String (fromString)
import Data.These (These (..))
import Data.Void (Void)
import Generics.Kind.TH (deriveGenericK)
import Hedgehog (Gen, Group (..), Property, PropertyName, checkSequential, forAll, property, (===))
import Hedgehog.Classes (Laws (..))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

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

-- | A bare function field @a -> r@, with no named contravariant wrapper.
-- Exercises the function atom directly; the 'Monoid' codomain gives it the
-- @Op r@ (Divisible/Decidable) instances.
newtype Sink a = Sink (a -> [String])

$(deriveGenericK ''Sink)

deriving via FromGeneric Sink instance Semigroupal (->) (,) (,) Sink

deriving via FromGeneric Sink instance Semigroupal (->) Either (,) Sink

deriving via FromGeneric Sink instance Unital (->) () () Sink

deriving via FromGeneric Sink instance Unital (->) Void () Sink

deriving via FromGeneric Sink instance Monoidal (->) (,) () (,) () Sink

deriving via FromGeneric Sink instance Monoidal (->) Either Void (,) () Sink

instance Contravariant Sink where
  contramap f (Sink g) = Sink (g . f)

runSink :: Sink a -> a -> [String]
runSink (Sink f) = f

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

-- Rank-2 tensor builders, for the contravariant law observation points.
genPairT :: Gen a -> Gen b -> Gen (a, b)
genPairT ga gb = (,) <$> ga <*> gb

genEitherT :: Gen a -> Gen b -> Gen (Either a b)
genEitherT ga gb = Gen.choice [Left <$> ga, Right <$> gb]

genTwoPreds :: Gen (TwoPreds Int)
genTwoPreds = TwoPreds <$> genPredInt <*> genPredInt
  where
    genPredInt = (\n -> Predicate (> n)) <$> genInt

genSink :: Gen (Sink Int)
genSink = (\n -> Sink (\x -> [show (x + n)])) <$> genInt

--------------------------------------------------------------------------------
-- Property laws

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

obsTwoPreds :: TwoPreds a -> a -> (Bool, Bool)
obsTwoPreds (TwoPreds p q) a = (getPredicate p a, getPredicate q a)

-- | The function atom divides its input across the two sinks at the product
-- tensor.
sinkDivide :: Property
sinkDivide = property $ do
  m <- forAll genInt
  n <- forAll genInt
  a <- forAll genInt
  b <- forAll genInt
  runSink (combine @(->) @(,) @(,) (Sink (\x -> [show (x + m)]), Sink (\x -> [show (x + n)]))) (a, b)
    === [show (a + m), show (b + n)]

-- | At the Either tensor the function atom chooses.
sinkChoose :: Property
sinkChoose = property $ do
  m <- forAll genInt
  n <- forAll genInt
  a <- forAll genInt
  let s = combine @(->) @Either @(,) (Sink (\x -> [show (x + m)]), Sink (\x -> [show (x + n)]))
  runSink s (Left a) === [show (a + m)]
  runSink s (Right a) === [show (a + n)]

--------------------------------------------------------------------------------
-- Concrete checks for the tensors the property laws do not cover

check :: (Eq a, Show a) => String -> a -> a -> IO Bool
check name got want
  | got == want = putStrLn ("ok   " ++ name) >> pure True
  | otherwise = putStrLn ("FAIL " ++ name ++ ": got " ++ show got ++ ", want " ++ show want) >> pure False

-- | Splice a sublibrary 'Laws' into the hedgehog 'Group', prefixing each of its
-- properties with the instance under test.
labeled :: String -> Laws -> [(PropertyName, Property)]
labeled prefix ls = [(fromString (prefix <> " " <> n), p) | (n, p) <- lawsProperties ls]

--------------------------------------------------------------------------------

tests :: IO Bool
tests = do
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
      Group "generic-deriving laws" $
        concat
          [ -- Covariant Monoidal, product tensor.
            labeled "Phantom (,)" (monoidalLaws @(,) @() genPhantom),
            labeled "Two (,)" (monoidalLaws @(,) @() genTwo),
            labeled "P (,)" (monoidalLaws @(,) @() genP),
            labeled "W (,)" (monoidalLaws @(,) @() genW),
            labeled "Nest (,)" (monoidalLaws @(,) @() genNest),
            labeled "Rec (,)" (monoidalLaws @(,) @() genRec),
            labeled "Mix (,)" (monoidalLaws @(,) @() genMix),
            -- Covariant Monoidal, Either tensor.
            labeled "P Either" (monoidalLaws @Either @Void genP),
            labeled "W Either" (monoidalLaws @Either @Void genW),
            labeled "Nest Either" (monoidalLaws @Either @Void genNest),
            -- Covariant Semigroupal only, These tensor.
            labeled "P These" (semigroupalLaws @These genP),
            -- Contravariant Monoidal.
            labeled "TwoPreds (,)" (contravariantMonoidalLaws @(,) @() genTwoPreds genPairT obsTwoPreds),
            labeled "Sink (,)" (contravariantMonoidalLaws @(,) @() genSink genPairT runSink),
            labeled "Sink Either" (contravariantMonoidalLaws @Either @Void genSink genEitherT runSink),
            -- Op (comonoidal) split.
            labeled "Two Op" (opSemigroupalLaws genTwo),
            labeled "P Op" (opSemigroupalLaws genP),
            labeled "Nest Op" (opSemigroupalLaws genNest),
            labeled "S Op" (opSemigroupalLaws genS),
            labeled "Sum3 Op" (opSemigroupalLaws genSum3),
            -- Op split / combine coherence, for the representable Two.
            labeled "Two" (representableSplitLaws genTwo)
          ]
          <> [ -- Concrete checks the general laws do not capture.
               ("reference P", referenceP),
               ("contravariant divide TwoPreds", contravariantTwoPreds),
               ("split unzip P", splitLaw @P genP),
               ("split unzip Nest", splitLaw @Nest genNest),
               ("split unzip S", splitLaw @S genS),
               ("split unzip Sum3", splitLaw @Sum3 genSum3),
               ("function atom divide Sink", sinkDivide),
               ("function atom choose Sink", sinkChoose)
             ]
  pure (and [u1, u2, u3, u4, u5] && props)
