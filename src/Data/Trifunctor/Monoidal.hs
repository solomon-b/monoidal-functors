module Data.Trifunctor.Monoidal where

import Control.Category.Tensor

class
  ( Associative t1 cat
  , Associative t2 cat
  , Associative t3 cat
  , Associative to cat
  ) => Semigroupal cat t1 t2 t3 to f where
  combine :: to (f x y z) (f x' y' z') `cat` f (t1 x x') (t2 y y') (t3 z z')

class Unital cat i1 i2 i3 o f where
  introduce :: o `cat` f i1 i2 i3

class
  ( Tensor t1 i1 cat
  , Tensor t2 i2 cat
  , Tensor t3 i3 cat
  , Tensor to io cat
  , Semigroupal cat t1 t2 t3 to f
  , Unital cat i1 i2 i3 io f
  ) => Monoidal cat t1 i1 t2 i2 t3 i3 to io f
