module Data.Functor.Monoidal where

import Control.Applicative
import Control.Category.Tensor
import Data.Void
import Prelude

-- | A <https://ncatlab.org/nlab/show/monoidal+functor Monoidal Functor> is a Functor between two Monoidal Categories
-- which preserves the monoidal structure. Eg., a homomorphism of
-- monoidal categories.
--
-- = Laws
-- Associativity:
--   combine (combine fx fy) fz ⟶ combine fx (combine fy fz)
--              ↓                         ↓
--   f (x `t1` y) `t1` fz         combine fx (f (y `t1` z))
--              ↓                         ↓
--   f ((x `t1` y) `t1` z)      ⟶ (f x `t1` (y `t1` z))
--
-- Left Unitality:
--   empty `t1` f x     ⟶  f empty `t1` f x
--         ↓                        ↓
--        f x           ←  f (empty `t0` x)
--
-- Right Unitality:
--   f x `t1` empty     ⟶  f x `t1` f empty
--         ↓                        ↓
--        f x           ←  f (x `t0` empty)
class
  ( Tensor cat t1 i1
  , Tensor cat t0 i0
  , Semigroupal cat t1 t0 f
  , Unital cat i1 i0 f
  ) => Monoidal cat t1 i1 t0 i0 f

class (Associative cat t1, Associative cat t0) => Semigroupal cat t1 t0 f where
  combine :: (f x `t0` f x') `cat` f (x `t1` x')

class Unital cat i1 i0 f where
  introduce :: i0 `cat` f i1

-- TODO: Should we create an Apply class?
instance Applicative f => Semigroupal (->) (,) (,) f where
  combine :: (f x, f x') -> f (x, x')
  combine = uncurry (liftA2 (,))

instance Applicative f => Unital (->) () () f where
  introduce :: () -> f ()
  introduce = pure

instance Applicative f => Monoidal (->) (,) () (,) () f

-- TODO: Should we create an Alt class?
instance Alternative f => Semigroupal (->) Either (,) f where
  combine :: (f x, f x') -> f (Either x x')
  combine (fx, fx') = fmap Left fx <|> fmap Right fx'

-- TODO: Should we create a Plus class?
instance Alternative f => Unital (->) Void () f where
  introduce :: () -> f Void
  introduce () = empty

instance Alternative f => Monoidal (->) Either Void (,) () f
