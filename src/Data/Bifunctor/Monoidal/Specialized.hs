module Data.Bifunctor.Monoidal.Specialized where

import Prelude hiding ((&&), (||))

import Control.Category.Tensor
import Data.Bifunctor.Monoidal
import Data.Profunctor

mux :: Semigroupal (->) (,) (,) (,) p => p a b -> p c d -> p (a, c) (b, d)
mux = curry combine


infixr 5 &&

(&&) :: Semigroupal (->) (,) (,) (,) p => p a b -> p c d -> p (a, c) (b, d)
(&&) = mux

zip :: (Profunctor p, Semigroupal (->) (,) (,) (,) p) => p x a -> p x b -> p x (a, b)
zip pxa pxb = lmap dup $ pxa && pxb

demux :: Semigroupal (->) Either Either (,) p => p a b -> p c d -> p (Either a c) (Either b d)
demux = curry combine

infixr 4 ||

(||) :: Semigroupal (->) Either Either (,) p => p a b -> p c d -> p (Either a c) (Either b d)
(||) = demux


fanin :: (Profunctor p, Semigroupal (->) Either Either (,) p) => p a x -> p b x -> p (Either a b) x
fanin pax pbx = rmap merge $ pax || pbx

switch :: Semigroupal (->) (,) Either (,) p => p a b -> p c d -> p (a, c) (Either b d)
switch = curry combine

infixr 5 &|

(&|) :: Semigroupal (->) (,) Either (,) p => p a b -> p c d -> p (a, c) (Either b d)
(&|) = switch

union :: Profunctor p => Semigroupal (->) (,) Either (,) p => p x a -> p x b -> p x (Either a b)
union pxa pxb = lmap dup $ pxa &| pxb
