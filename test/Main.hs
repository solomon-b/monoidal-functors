{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Main (main) where

import Control.Monad (unless)
import Data.Functor.Contravariant (Predicate (..))
import Data.Functor.Monoidal (Semigroupal (..))
import Data.Functor.Monoidal.Generic (GenericallyK (..))
import Data.These (These (..))
import Generics.Kind.TH (deriveGenericK)
import System.Exit (exitFailure)

-- | A bare parameter. Exercises @Field Var0@.
data Two a = Two a a deriving (Functor, Show, Eq)

$(deriveGenericK ''Two)

deriving via GenericallyK Two instance Semigroupal (->) (,) (,) Two

-- | Sub-functor fields. Exercises @Field (Kon g :@: Var0)@ with covariant leaves.
data P a = P (Maybe a) [a] deriving (Functor, Show, Eq)

$(deriveGenericK ''P)

deriving via GenericallyK P instance Semigroupal (->) (,) (,) P

deriving via GenericallyK P instance Semigroupal (->) Either (,) P

deriving via GenericallyK P instance Semigroupal (->) These (,) P

-- | A constant 'Monoid' field. Exercises @Field (Kon c)@.
data W a = W String (Maybe a) deriving (Functor, Show, Eq)

$(deriveGenericK ''W)

deriving via GenericallyK W instance Semigroupal (->) (,) (,) W

-- | A contravariant functor. Exercises @Field (Kon Predicate :@: Var0)@.
data TwoPreds a = TwoPreds (Predicate a) (Predicate a)

$(deriveGenericK ''TwoPreds)

deriving via GenericallyK TwoPreds instance Semigroupal (->) (,) (,) TwoPreds

check :: (Eq a, Show a) => String -> a -> a -> IO Bool
check name got want
  | got == want = putStrLn ("ok   " ++ name) >> pure True
  | otherwise = putStrLn ("FAIL " ++ name ++ ": got " ++ show got ++ ", want " ++ show want) >> pure False

main :: IO ()
main = do
  r1 <-
    check
      "Two (bare parameter)"
      (combine @(->) @(,) @(,) (Two 1 2, Two 3 4))
      (Two (1, 3) (2, 4) :: Two (Int, Int))
  r2 <-
    check
      "P (sub-functors)"
      (combine @(->) @(,) @(,) (P (Just 1) [1, 2], P (Just 2) [3, 4]))
      (P (Just (1, 2)) [(1, 3), (1, 4), (2, 3), (2, 4)] :: P (Int, Int))
  r3 <-
    check
      "W (Monoid constant)"
      (combine @(->) @(,) @(,) (W "a" (Just 1), W "b" (Just 2)))
      (W "ab" (Just (1, 2)) :: W (Int, Int))
  r4 <- do
    let TwoPreds f g =
          combine @(->) @(,) @(,)
            ( TwoPreds (Predicate even) (Predicate (> 0)),
              TwoPreds (Predicate odd) (Predicate (< 10))
            )
    check
      "TwoPreds (contravariant)"
      (getPredicate f (2, 3), getPredicate f (2, 4), getPredicate g (5 :: Int, 5))
      (True, False, True)
  r5 <-
    check
      "P (Either tensor)"
      (combine @(->) @Either @(,) (P (Just 1) [1, 2], P (Just 3) [4]))
      (P (Just (Left 1)) [Left 1, Left 2, Right 4] :: P (Either Int Int))
  r6 <-
    check
      "P (These tensor)"
      (combine @(->) @These @(,) (P (Just 1) [1, 2], P (Just 3) [4]))
      (P (Just (These 1 3)) [These 1 4, This 2] :: P (These Int Int))
  unless (and [r1, r2, r3, r4, r5, r6]) exitFailure
