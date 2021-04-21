module Data.Bifunctor.Monoidal where

import Prelude hiding ((.), id)
import Control.Category
import Control.Category.Tensor
import Data.Bifunctor
import Data.Profunctor

class (Associative t1 cat, Associative t2 cat, Associative to cat) => Semigroupal cat t1 t2 to f where
  combine :: cat (to (f x y) (f x' y')) (f (t1 x x') (t2 y y'))

instance Profunctor p => Semigroupal (->) (,) Either Either p where
  combine :: Either (p x y) (p x' y') -> p (x, x') (Either y y')
  combine = either (dimap fst Left) (dimap snd Right)

instance Semigroupal (->) (,) (,) (,) (,) where
  combine :: ((x, y), (x', y')) -> ((x, x'), (y, y'))
  combine ((x, y), (x', y')) = ((x, x'), (y, y'))
  -- NOTE: This version could be used for a more general abstraction
  -- of products in a category:
  -- combine =
  --   let fwd' = fwd assoc
  --       bwd' = bwd assoc
  --   in second swap . swap . fwd' . swap . first (bwd' . first swap) . fwd'

instance Semigroupal (->) Either Either Either (,) where
  combine :: Either (x, y) (x', y') -> (Either x x', Either y y')
  combine = either (bimap Left Left) (bimap Right Right)

instance Semigroupal (->) Either Either Either Either where
  combine :: Either (Either x y) (Either x' y') -> Either (Either x x') (Either y y')
  combine = either (bimap Left Left) (bimap Right Right)

instance Semigroupal (->) Either (,) (,) Either where
  combine :: (Either x y, Either x' y') -> Either (Either x x') (y, y')
  combine (l, r) = undefined
