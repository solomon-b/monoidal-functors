-- | Test driver. Runs the generic-deriving suite, the rank-2 traversable
-- specs, and the laws sublibrary self-test, and fails if any does.
module Main (main) where

import Control.Category.CartesianSpec qualified as CartesianSpec
import Control.Category.TensorSpec qualified as TensorSpec
import Control.Monad (unless)
import Data.Bifunctor.Monoidal.LawsSpec qualified as BifunctorLawsSpec
import Data.Bifunctor.Rank2.TraversableSpec qualified as BifunctorTraversableSpec
import Data.Functor.Monoidal.GenericSpec qualified as GenericSpec
import Data.Functor.Monoidal.LawsSpec qualified as LawsSpec
import Data.Functor.Rank2.TraversableSpec qualified as FunctorTraversableSpec
import Data.Trifunctor.Rank2.TraversableSpec qualified as TrifunctorTraversableSpec
import System.Exit (exitFailure)
import Prelude

--------------------------------------------------------------------------------

main :: IO ()
main = do
  results <-
    sequence
      [ putStrLn "=== Control.Category.Tensor laws ===" *> TensorSpec.tests,
        putStrLn "=== Control.Category.Cartesian laws ===" *> CartesianSpec.tests,
        putStrLn "=== bifunctor monoidal laws ===" *> BifunctorLawsSpec.tests,
        putStrLn "=== generic deriving ===" *> GenericSpec.tests,
        putStrLn "=== rank-2 traversable ===" *> FunctorTraversableSpec.tests,
        BifunctorTraversableSpec.tests,
        TrifunctorTraversableSpec.tests,
        putStrLn "=== laws sublibrary self-test ===" *> LawsSpec.tests
      ]
  unless (and results) exitFailure
