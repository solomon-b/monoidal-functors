module Data.Bifunctor.Monoidal.Specialized where

import Prelude hiding ((&&), (||))

import Control.Category.Tensor
import Data.Bifunctor.Monoidal
import Data.Functor.Contravariant
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

divide :: (Profunctor p, Semigroupal (->) (,) Either (,) p) => p a x -> p b x -> p (a, b) x
divide pxa pxb = rmap merge $ pxa &| pxb

splice :: Semigroupal (->) Either (,) (,) p => p a b -> p c d -> p (Either a c) (b, d)
splice = curry combine

infix 5 |&

(|&) :: Semigroupal (->) Either (,) (,) p => p a b -> p c d -> p (Either a c) (b, d)
(|&) = splice

diverge :: Semigroupal (->) Either Either Either p => Either (p a b) (p c d) -> p (Either a c) (Either b d)
diverge = combine

contramapMaybe :: Profunctor p => Semigroupal (->) Either Either Either p => (a -> Maybe b) -> p b x -> p a x
contramapMaybe f = dimap (maybe (Right ()) Left . f) merge . ultraleft

zig :: (Profunctor p, Semigroupal (->) (,) t Either p) => Either (p x a) (p x b) -> p x (t a b)
zig = lmap dup . combine

zag :: (Profunctor p, Semigroupal (->) t Either Either p) => Either (p a x) (p b x) -> p (t a b) x
zag = rmap merge . combine

ultrafirst :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (a, x) (b, y)
ultrafirst = zag . Left . zig . Left

ultrasecond :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (x, a) (y, b)
ultrasecond = zag . Right . zig . Right

ultraleft :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either a x) (Either b y)
ultraleft = zag . Left . zig . Left

ultraright :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either x a) (Either y b)
ultraright = zag . Right . zig . Right

--comux :: forall p a b c d. Semigroupal Op (,) (,) (,) p => p (a, c) (b, d) -> (p a b, p c d)
--comux = getOp Op (combine @Op @(,) @(,) @(,) @p)
