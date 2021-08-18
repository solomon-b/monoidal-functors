module Data.Functor.Monoidal where

import Prelude
import Control.Applicative
import Control.Category.Tensor
import Data.Void

class (Associative t1 cat, Associative t0 cat) => Semigroupal cat t1 t0 f where
  combine :: (f x `t0` f x') `cat` f (x `t1` x')

class Unital cat i1 i0 f where
  introduce :: i0 `cat` f i1

class ( Tensor t1 i1 cat
      , Tensor t0 i0 cat
      , Semigroupal cat t1 t0 f
      , Unital cat i1 i0 f
      ) => Monoidal cat t1 i1 t0 i0 f

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
