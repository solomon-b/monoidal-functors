module Data.Functor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal (..),
  )
where

import Control.Applicative
import Control.Category.Tensor
import Data.Align
import Data.These
import Data.Void
import Prelude

--------------------------------------------------------------------------------

-- | TODO
--
-- === Laws
--
-- @
-- TODO
-- @
class (Associative cat t1, Associative cat t0) => Semigroupal cat t1 t0 f where
  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Just "hello")
  -- Just (True,"hello")
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Nothing)
  -- Nothing
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Just True, Nothing)
  -- Just (Left True)
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Nothing, Just "hello")
  -- Just (Right "hello")
  combine :: (f x `t0` f x') `cat` f (x `t1` x')

instance Applicative f => Semigroupal (->) (,) (,) f where
  combine :: (f x, f x') -> f (x, x')
  combine = uncurry (liftA2 (,))

instance Alternative f => Semigroupal (->) Either (,) f where
  combine :: (f x, f x') -> f (Either x x')
  combine (fx, fx') = fmap Left fx <|> fmap Right fx'

instance Semialign f => Semigroupal (->) These (,) f where
  combine :: (f x, f x') -> f (These x x')
  combine = uncurry align

--------------------------------------------------------------------------------

-- | TODO
--
-- __Laws:__
--
-- @
-- TODO
-- @
class Unital cat i1 i0 f where
  -- | TODO
  --
  -- ==== __Examples__
  --
  -- >>> introduce @(->) @() @() @Maybe ()
  -- Just ()
  --
  -- >>> :t introduce @(->) @Void @() @Maybe 
  -- introduce @(->) @Void @() @Maybe :: () -> Maybe Void
  -- 
  -- >>> introduce @(->) @Void @() @Maybe ()
  -- Nothing
  introduce :: cat i0 (f i1)

instance Applicative f => Unital (->) () () f where
  introduce :: () -> f ()
  introduce = pure

instance Alternative f => Unital (->) Void () f where
  introduce :: () -> f Void
  introduce () = empty
  
--------------------------------------------------------------------------------
-- Tensor

-- | A <https://ncatlab.org/nlab/show/monoidal+functor Monoidal Functor> is a Functor between two Monoidal Categories
-- which preserves the monoidal structure. Eg., a homomorphism of
-- monoidal categories.
--
-- === Laws
--
-- @
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
-- @
class
  ( Tensor cat t1 i1
  , Tensor cat t0 i0
  , Semigroupal cat t1 t0 f
  , Unital cat i1 i0 f
  ) => Monoidal cat t1 i1 t0 i0 f

instance Applicative f => Monoidal (->) (,) () (,) () f

instance Alternative f => Monoidal (->) Either Void (,) () f
