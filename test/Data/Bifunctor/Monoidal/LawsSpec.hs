{-# LANGUAGE OverloadedStrings #-}

-- | Self-test: run the exported "Data.Bifunctor.Monoidal.Laws" 'Laws' against
-- known-good instances — covariant bifunctors (tuples, which exercise both
-- tensor positions with a full 'Eq') and profunctors (@('->')@, @'Star' 'Maybe'@,
-- @'Kleisli' 'Maybe'@, observed extensionally).
module Data.Bifunctor.Monoidal.LawsSpec (tests) where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Data.Bifunctor.Monoidal.Laws (monoidalLaws, profunctorMonoidalLaws)
import Data.Functor.Identity (Identity (..))
import Data.Profunctor (Star (..))
import Data.String (fromString)
import Data.Void (Void)
import Hedgehog (Gen, Group (..), Property, PropertyName, checkSequential)
import Hedgehog.Classes (Laws (..))
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Prelude

--------------------------------------------------------------------------------

genInt :: Gen Int
genInt = Gen.int (Range.linear (-100) 100)

-- Covariant bifunctor generators. The @()@ leading components are the 'Monoid'
-- tags the @(,,)@ \/ @(,,,)@ instances carry.

genPair :: Gen a -> Gen b -> Gen (a, b)
genPair ga gb = (,) <$> ga <*> gb

genTriple :: Gen a -> Gen b -> Gen ((), a, b)
genTriple ga gb = (\a b -> ((), a, b)) <$> ga <*> gb

genQuad :: Gen a -> Gen b -> Gen ((), (), a, b)
genQuad ga gb = (\a b -> ((), (), a, b)) <$> ga <*> gb

-- Profunctor observers and (opaque) value generators.

runFun :: (a -> b) -> a -> Identity b
runFun f = Identity . f

runStarMaybe :: Star Maybe a b -> a -> Maybe b
runStarMaybe = runStar

runKleisliMaybe :: Kleisli Maybe a b -> a -> Maybe b
runKleisliMaybe = runKleisli

genFun :: Gen (Int -> Int)
genFun = Gen.choice [(\n -> (+ n)) <$> genInt, (\n -> (n -)) <$> genInt, (\n -> (* n)) <$> genInt]

genStar :: Gen (Star Maybe Int Int)
genStar =
  Gen.choice
    [ (\n -> Star (\x -> Just (x + n))) <$> genInt,
      (\n -> Star (\x -> if even x then Just (x * n) else Nothing)) <$> genInt
    ]

genKleisli :: Gen (Kleisli Maybe Int Int)
genKleisli =
  Gen.choice
    [ (\n -> Kleisli (\x -> Just (x + n))) <$> genInt,
      (\n -> Kleisli (\x -> if even x then Just (x * n) else Nothing)) <$> genInt
    ]

-- Rank-2 tensor builders for the profunctors' contravariant-side inputs.

genPairT :: Gen x -> Gen y -> Gen (x, y)
genPairT gx gy = (,) <$> gx <*> gy

genEitherT :: Gen x -> Gen y -> Gen (Either x y)
genEitherT gx gy = Gen.choice [Left <$> gx, Right <$> gy]

-- | Splice a sublibrary 'Laws' into the hedgehog 'Group', prefixing each of its
-- properties with the instance under test.
labeled :: String -> Laws -> [(PropertyName, Property)]
labeled prefix ls = [(fromString (prefix <> " " <> n), p) | (n, p) <- lawsProperties ls]

--------------------------------------------------------------------------------

tests :: IO Bool
tests = do
  covariant <-
    checkSequential $
      Group "Bifunctor monoidal laws (covariant)" $
        concat
          [ labeled "(,)" (monoidalLaws @(,) @() @(,) @() genPair),
            labeled "(,,) ()" (monoidalLaws @(,) @() @(,) @() genTriple),
            labeled "(,,,) () ()" (monoidalLaws @(,) @() @(,) @() genQuad)
          ]
  profunctor <-
    checkSequential $
      Group "Bifunctor monoidal laws (profunctor)" $
        concat
          [ labeled "(->) (,)" (profunctorMonoidalLaws @(,) @() @(,) @() runFun genFun genPairT),
            labeled "(->) Either" (profunctorMonoidalLaws @Either @Void @Either @Void runFun genFun genEitherT),
            labeled "Star Maybe (,)" (profunctorMonoidalLaws @(,) @() @(,) @() runStarMaybe genStar genPairT),
            labeled "Kleisli Maybe (,)" (profunctorMonoidalLaws @(,) @() @(,) @() runKleisliMaybe genKleisli genPairT)
          ]
  pure (covariant && profunctor)
