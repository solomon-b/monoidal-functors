{-# LANGUAGE MonoLocalBinds #-}
module Control.Category.Cartesian where

import Control.Category (id, (>>>))
import Data.Functor.Contravariant
import Data.Void
import Prelude hiding (id)

import Control.Category.Tensor


class Symmetric cat t => Semicartesian cat t where
  split :: cat a (a `t` a)

  fork :: cat a x -> cat a y -> cat a (x `t` y)
  fork f g = split >>> f # g

  {-# MINIMAL split #-}

class Symmetric cat t => Semicocartesian cat t where
  merge :: cat (a `t` a) a

  fuse :: cat x a -> cat y a -> cat (x `t` y) a
  fuse f g = f # g >>> merge

  {-# MINIMAL merge #-}


infixr 9 /\
(/\) :: Semicartesian cat t =>  cat a x -> cat a y -> cat a (x `t` y)
(/\) = fork

infixr 9 \/
(\/) :: Semicocartesian cat t => cat x a -> cat y a -> cat (x `t` y) a
(\/) = fuse


instance Semicartesian (->) t => Semicocartesian Op t where
  merge = Op split

instance Semicocartesian (->) t => Semicartesian Op t where
  split = Op merge


instance Semicartesian (->) (,) where
  split :: a -> (a, a)
  split    a =  (a, a)

instance Semicocartesian (->) Either where
  merge :: Either a a -> a
  merge =  either id id


class (Semicartesian cat t, Tensor cat t i) => Cartesian cat t i | i -> t, t -> i where
  kill :: cat a i

  projl :: cat (x `t` y) x
  projl = id # kill >>> fwd unitr

  projr :: cat (x `t` y) y
  projr = kill # id >>> fwd unitl

  unfork :: cat a (x `t` y) -> (cat a x, cat a y)
  unfork h = (h >>> projl, h >>> projr)

  {-# MINIMAL kill #-}


class (Semicocartesian cat t, Tensor cat t i) => Cocartesian cat t i | i -> t, t -> i where
  spawn :: cat i a

  incll :: cat x (x `t` y)
  incll = bwd unitr >>> id # spawn

  inclr :: cat y (x `t` y)
  inclr = bwd unitl >>> spawn # id

  unfuse :: cat (x `t` y) a -> (cat x a, cat y a)
  unfuse h = (incll >>> h, inclr >>> h)

  {-# MINIMAL spawn #-}


instance Cartesian (->) t i => Cocartesian Op t i where
  spawn = Op kill

instance Cocartesian (->) t i => Cartesian Op t i where
  kill = Op spawn


instance Cartesian (->) (,) () where
  kill :: a -> ()
  kill = const ()

instance Cocartesian (->) Either Void where
  spawn :: Void -> a
  spawn = absurd
