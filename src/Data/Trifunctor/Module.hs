module Data.Trifunctor.Module where

--------------------------------------------------------------------------------
-- LeftModule

class LeftModule cat t1 t2 t3 f where
  lstrength :: cat (f a b c) (f (t1 a x) (t2 b x) (t3 c x))

--------------------------------------------------------------------------------
-- RightModule

class RightModule cat t1 t2 t3 f where
  rstrength :: cat (f a b c) (f (t1 x a) (t2 x b) (t3 x c))

--------------------------------------------------------------------------------
-- Bimodule

class (LeftModule cat t1 t2 t3 f, RightModule cat t1 t2 t3 f) => Bimodule cat t1 t2 t3 f
