module Data.Trifunctor.Monoidal where

import Control.Category.Tensor

--------------------------------------------------------------------------------
-- Semigroupal

class
  ( Associative cat t1
  , Associative cat t2
  , Associative cat t3
  , Associative cat to
  ) => Semigroupal cat t1 t2 t3 to f where
  combine :: to (f x y z) (f x' y' z') `cat` f (t1 x x') (t2 y y') (t3 z z')

--------------------------------------------------------------------------------
-- Unital

class Unital cat i1 i2 i3 o f where
  introduce :: o `cat` f i1 i2 i3

--------------------------------------------------------------------------------
-- Monoidal

class
  ( Tensor cat t1 i1
  , Tensor cat t2 i2
  , Tensor cat t3 i3
  , Tensor cat to io
  , Semigroupal cat t1 t2 t3 to f
  , Unital cat i1 i2 i3 io f
  ) => Monoidal cat t1 i1 t2 i2 t3 i3 to io f
