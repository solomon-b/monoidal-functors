{-# LANGUAGE OverloadedStrings #-}

-- | Runs the exported "Data.Bifunctor.Monoidal.Laws" 'Laws' against
-- known-good instances. Covariant bifunctors (tuples, which exercise both
-- tensor positions with a full 'Eq') and profunctors (@('->')@, @'Star' 'Maybe'@,
-- @'Kleisli' 'Maybe'@, observed extensionally).
module Data.Bifunctor.Monoidal.LawsSpec (tests) where

--------------------------------------------------------------------------------

import Control.Arrow (Kleisli (..))
import Control.Category.Tensor (Associative (assoc), Iso (bwd))
import Data.Bifunctor (bimap)
import Data.Bifunctor.Biap (Biap (..))
import Data.Bifunctor.Biff (Biff (..))
import Data.Bifunctor.Clown (Clown (..))
import Data.Bifunctor.Flip (Flip (..))
import Data.Bifunctor.Joker (Joker (..))
import Data.Bifunctor.Monoidal (Semigroupal (combine))
import Data.Bifunctor.Monoidal.Laws (monoidalLaws, opSemigroupalLaws, profunctorMonoidalLaws)
import Data.Bifunctor.Product (Product (..))
import Data.Bifunctor.Tannen (Tannen (..))
import Data.Bifunctor.Wrapped (WrappedBifunctor (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Contravariant (Op (..))
import Data.Functor.Identity (Identity (..))
import Data.Tagged (Tagged (..))
import Data.These (These (..))
import Data.Profunctor (Forget (..), Star (..), lmap)
import Data.Semigroup (Arg (..))
import Data.String (fromString)
import Data.Void (Void)
import Hedgehog (Gen, Group (..), Property, PropertyName, checkSequential, forAll, forAllWith, property, (===))
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

genQuint :: Gen a -> Gen b -> Gen ((), (), (), a, b)
genQuint ga gb = (\a b -> ((), (), (), a, b)) <$> ga <*> gb

genSext :: Gen a -> Gen b -> Gen ((), (), (), (), a, b)
genSext ga gb = (\a b -> ((), (), (), (), a, b)) <$> ga <*> gb

genSept :: Gen a -> Gen b -> Gen ((), (), (), (), (), a, b)
genSept ga gb = (\a b -> ((), (), (), (), (), a, b)) <$> ga <*> gb

-- 'Arg's 'Eq' compares only the first parameter, so this law test is weaker than
-- the others (it cannot observe the second-parameter handling).
genArg :: Gen a -> Gen b -> Gen (Arg a b)
genArg ga gb = Arg <$> ga <*> gb

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

genConstB :: Gen a -> Gen b -> Gen (Const a b)
genConstB ga _ = Const <$> ga

genTaggedB :: Gen a -> Gen b -> Gen (Tagged a b)
genTaggedB _ gb = Tagged <$> gb

genProduct :: Gen a -> Gen b -> Gen (Product (,) (,) a b)
genProduct ga gb = Pair <$> genPair ga gb <*> genPair ga gb

genThese :: Gen a -> Gen b -> Gen (These a b)
genThese ga gb = Gen.choice [This <$> ga, That <$> gb, These <$> ga <*> gb]

genJokerMaybe :: Gen a -> Gen b -> Gen (Joker Maybe a b)
genJokerMaybe _ gb = Joker <$> Gen.maybe gb

genClownMaybe :: Gen a -> Gen b -> Gen (Clown Maybe a b)
genClownMaybe ga _ = Clown <$> Gen.maybe ga

genBiap :: Gen a -> Gen b -> Gen (Biap (,) a b)
genBiap ga gb = Biap <$> genPair ga gb

genWrapped :: Gen a -> Gen b -> Gen (WrappedBifunctor (,) a b)
genWrapped ga gb = WrapBifunctor <$> genPair ga gb

genFlip :: Gen a -> Gen b -> Gen (Flip (,) a b)
genFlip ga gb = Flip <$> genPair gb ga

genTannen :: Gen a -> Gen b -> Gen (Tannen Identity Either a b)
genTannen ga gb = (Tannen . Identity) <$> genEitherT ga gb

genBiff :: Gen a -> Gen b -> Gen (Biff (,) Maybe Maybe a b)
genBiff ga gb = Biff <$> genPair (Gen.maybe ga) (Gen.maybe gb)

-- Ad-hoc witnesses for the 'Forget' colax split. The generic law cannot exercise
-- it (the split consumes profunctors at structured contravariant-argument types),
-- but at fixed 'Either' types every function factors through its branches, so the
-- split is testable by observation. Fixed at @Forget (Maybe Int)@.

genBranch :: Gen (Int -> Maybe Int)
genBranch =
  Gen.choice
    [ (\n x -> Just (x + n)) <$> genInt,
      (\n x -> if even x then Just (x * n) else Nothing) <$> genInt,
      pure (const Nothing)
    ]

splitForget :: Forget (Maybe Int) (Either x x') (Either y y') -> (Forget (Maybe Int) x y, Forget (Maybe Int) x' y')
splitForget = getOp (combine @Op @Either @Either @(,))

combineForget :: (Forget (Maybe Int) x y, Forget (Maybe Int) x' y') -> Forget (Maybe Int) (Either x x') (Either y y')
combineForget = combine @(->) @Either @Either @(,)

genEitherT :: Gen x -> Gen y -> Gen (Either x y)
genEitherT gx gy = Gen.choice [Left <$> gx, Right <$> gy]

-- | Splices a sublibrary 'Laws' into the hedgehog 'Group', prefixing each of its
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
  colax <-
    checkSequential $
      Group "Bifunctor monoidal laws (colax Op)" $
        concat
          [ labeled "(,)" (opSemigroupalLaws @(,) @(,) @(,) genPair genPairT genPairT),
            labeled "Either" (opSemigroupalLaws @Either @Either @Either genEitherT genEitherT genEitherT),
            labeled "(,,) ()" (opSemigroupalLaws @(,) @(,) @(,) genTriple genPairT genPairT),
            labeled "(,,,) () ()" (opSemigroupalLaws @(,) @(,) @(,) genQuad genPairT genPairT),
            labeled "(,,,,) () () ()" (opSemigroupalLaws @(,) @(,) @(,) genQuint genPairT genPairT),
            labeled "(,,,,,) () () () ()" (opSemigroupalLaws @(,) @(,) @(,) genSext genPairT genPairT),
            labeled "(,,,,,,) () () () () ()" (opSemigroupalLaws @(,) @(,) @(,) genSept genPairT genPairT),
            labeled "Arg" (opSemigroupalLaws @(,) @(,) @(,) genArg genPairT genPairT),
            labeled "Const" (opSemigroupalLaws @(,) @(,) @(,) genConstB genPairT genPairT),
            labeled "Tagged" (opSemigroupalLaws @(,) @(,) @(,) genTaggedB genPairT genPairT),
            labeled "Product (,) (,)" (opSemigroupalLaws @(,) @(,) @(,) genProduct genPairT genPairT),
            labeled "Joker Maybe" (opSemigroupalLaws @(,) @These @(,) genJokerMaybe genPairT genThese),
            labeled "Clown Maybe" (opSemigroupalLaws @These @(,) @(,) genClownMaybe genThese genPairT),
            labeled "Biap (,)" (opSemigroupalLaws @(,) @(,) @(,) genBiap genPairT genPairT),
            labeled "WrappedBifunctor (,)" (opSemigroupalLaws @(,) @(,) @(,) genWrapped genPairT genPairT),
            labeled "Flip (,)" (opSemigroupalLaws @(,) @(,) @(,) genFlip genPairT genPairT),
            labeled "Tannen Identity Either" (opSemigroupalLaws @Either @Either @Either genTannen genEitherT genEitherT),
            labeled "Biff (,) Maybe Maybe" (opSemigroupalLaws @These @These @(,) genBiff genThese genThese)
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
  forget <-
    checkSequential $
      Group
        "Bifunctor colax Op (Forget, ad-hoc)"
        [ ( "split . combine = id",
            property $ do
              f <- forAllWith (const "<fn>") genBranch
              g <- forAllWith (const "<fn>") genBranch
              x <- forAll genInt
              y <- forAll genInt
              let (p1, p2) = splitForget (combineForget (Forget f, Forget g))
              (runForget p1 x, runForget p2 y) === (f x, g y)
          ),
          ( "combine . split = id",
            property $ do
              f <- forAllWith (const "<fn>") genBranch
              g <- forAllWith (const "<fn>") genBranch
              e <- forAll (genEitherT genInt genInt)
              let h = either f g
              runForget (combineForget (splitForget (Forget h))) e === h e
          ),
          ( "Coassociativity",
            property $ do
              f <- forAllWith (const "<fn>") genBranch
              g <- forAllWith (const "<fn>") genBranch
              k <- forAllWith (const "<fn>") genBranch
              ia <- forAll genInt
              ib <- forAll genInt
              ic <- forAll genInt
              let h = either f (either g k) :: Either Int (Either Int Int) -> Maybe Int
                  (pa, pbc) = splitForget (Forget h :: Forget (Maybe Int) (Either Int (Either Int Int)) (Either Int (Either Int Int)))
                  (pb, pc) = splitForget pbc
                  h' = h . bwd (assoc @(->) @Either)
                  (pab, pc') = splitForget (Forget h' :: Forget (Maybe Int) (Either (Either Int Int) Int) (Either (Either Int Int) Int))
                  (pa', pb') = splitForget pab
              (runForget pa ia, runForget pb ib, runForget pc ic)
                === (runForget pa' ia, runForget pb' ib, runForget pc' ic)
          ),
          ( "Conaturality",
            property $ do
              f <- forAllWith (const "<fn>") genBranch
              g <- forAllWith (const "<fn>") genBranch
              x <- forAll genInt
              y <- forAll genInt
              let l = (+ 1) :: Int -> Int
                  h = either f g :: Either Int Int -> Maybe Int
                  (l1, l2) = splitForget (Forget (h . bimap l l) :: Forget (Maybe Int) (Either Int Int) (Either Int Int))
                  (r1, r2) = splitForget (Forget h :: Forget (Maybe Int) (Either Int Int) (Either Int Int))
              (runForget l1 x, runForget l2 y) === (runForget (lmap l r1) x, runForget (lmap l r2) y)
          )
        ]
  pure (covariant && colax && profunctor && forget)
