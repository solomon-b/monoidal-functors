{-# LANGUAGE TupleSections #-}

module Data.Bifunctor.Monoidal.Specialized where

--------------------------------------------------------------------------------

import Control.Category.Cartesian
import Control.Category.Tensor ()
import Data.Bifunctor
import Data.Bifunctor.Monoidal
import Data.Functor.Contravariant
import Data.Profunctor
import Data.Void
import Prelude hiding ((&&), (||))

--------------------------------------------------------------------------------

-- | Split the input between the two arguments and multiply their outputs.
mux :: Semigroupal (->) (,) (,) (,) p => p a b -> p c d -> p (a, c) (b, d)
mux = curry combine

infixr 3 ***

-- | Infix operator for 'mux'.
(***) :: Semigroupal (->) (,) (,) (,) p => p a b -> p c d -> p (a, c) (b, d)
(***) = mux

-- | Split the input between the two arguments and sum their outputs.
demux :: Semigroupal (->) Either Either (,) p => p a b -> p c d -> p (Either a c) (Either b d)
demux = curry combine

infixr 2 +++

-- | Infix operator for 'demux'.
(+++) :: Semigroupal (->) Either Either (,) p => p a b -> p c d -> p (Either a c) (Either b d)
(+++) = demux

-- | Send the whole input to the two arguments and multiply their outputs.
fanout :: (Profunctor p, Semigroupal (->) (,) (,) (,) p) => p x a -> p x b -> p x (a, b)
fanout pxa pxb = lmap split' $ pxa *** pxb

infixr 3 &&&

-- | Infix operator for 'fanout'.
(&&&) :: (Profunctor p, Semigroupal (->) (,) (,) (,) p) => p x a -> p x b -> p x (a, b)
(&&&) = fanout

-- | Split the input between the two arguments and merge their outputs.
fanin :: (Profunctor p, Semigroupal (->) Either Either (,) p) => p a x -> p b x -> p (Either a b) x
fanin pax pbx = rmap merge' $ pax +++ pbx

infixr 2 |||

-- | Infix operator for 'fanin'.
(|||) :: (Profunctor p, Semigroupal (->) Either Either (,) p) => p a x -> p b x -> p (Either a b) x
(|||) = fanin

-- | Split the input between the two arguments and and sum their outputs.
switch :: Semigroupal (->) (,) Either (,) p => p a b -> p c d -> p (a, c) (Either b d)
switch = curry combine

infixr 5 &|

-- | Infix operator for 'switch'.
(&|) :: Semigroupal (->) (,) Either (,) p => p a b -> p c d -> p (a, c) (Either b d)
(&|) = switch

-- | Send the whole input to the two arguments and sum their outputs.
union :: Profunctor p => Semigroupal (->) (,) Either (,) p => p x a -> p x b -> p x (Either a b)
union pxa pxb = lmap split' $ pxa &| pxb

-- | Split the input between the two arguments then merge their outputs.
divide :: (Profunctor p, Semigroupal (->) (,) Either (,) p) => p a x -> p b x -> p (a, b) x
divide pxa pxb = rmap merge' $ pxa &| pxb

-- | Split the input between the two arguments then multiply their outputs.
splice :: Semigroupal (->) Either (,) (,) p => p a b -> p c d -> p (Either a c) (b, d)
splice = curry combine

infix 5 |&

-- | Infix operator for 'splice'.
(|&) :: Semigroupal (->) Either (,) (,) p => p a b -> p c d -> p (Either a c) (b, d)
(|&) = splice

diverge :: Semigroupal (->) Either Either Either p => Either (p a b) (p c d) -> p (Either a c) (Either b d)
diverge = combine

contramapMaybe :: Profunctor p => Semigroupal (->) Either Either Either p => (a -> Maybe b) -> p b x -> p a x
contramapMaybe f = dimap (maybe (Right ()) Left . f) merge' . ultraleft

zig :: (Profunctor p, Semigroupal (->) (,) t Either p) => Either (p x a) (p x b) -> p x (t a b)
zig = lmap split' . combine

zag :: (Profunctor p, Semigroupal (->) t Either Either p) => Either (p a x) (p b x) -> p (t a b) x
zag = rmap merge' . combine

ultrafirst :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (a, x) (b, y)
ultrafirst = zag . Left . zig . Left

ultrasecond :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (x, a) (y, b)
ultrasecond = zag . Right . zig . Right

ultraleft :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either a x) (Either b y)
ultraleft = zag . Left . zig . Left

ultraright :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either x a) (Either y b)
ultraright = zag . Right . zig . Right

comux :: forall p a b c d. Semigroupal Op (,) (,) (,) p => p (a, c) (b, d) -> (p a b, p c d)
comux = getOp combine

undivide :: forall p x a b. Profunctor p => Semigroupal Op (,) (,) (,) p => p (a, b) x -> (p a x, p b x)
undivide = comux . rmap split'

codemux :: forall p a b c d. Semigroupal Op Either Either (,) p => p (Either a c) (Either b d) -> (p a b, p c d)
codemux = getOp combine

partition :: forall p x a b. Profunctor p => Semigroupal Op Either Either (,) p => p x (Either a b) -> (p x a, p x b)
partition = codemux . lmap merge'

coswitch :: forall p a b c d. Semigroupal Op Either (,) (,) p => p (Either a c) (b, d) -> (p a b, p c d)
coswitch = getOp combine

unfanin :: forall p x a b. Profunctor p => Semigroupal Op Either (,) (,) p => p (Either a b) x -> (p a x, p b x)
unfanin = coswitch . rmap split'

unzip :: forall p x a b. Profunctor p => Semigroupal Op Either (,) (,) p => p x (a, b) -> (p x a, p x b)
unzip = coswitch . lmap merge'

cosplice :: forall p a b c d. Semigroupal Op (,) Either (,) p => p (a, c) (Either b d) -> (p a b, p c d)
cosplice = getOp combine

terminal :: forall p a. Profunctor p => Unital (->) () () () p => p a ()
terminal = lmap (const ()) $ introduce ()

ppure :: forall p a. Profunctor p => Unital (->) () () () p => Strong p => p a a
ppure = dimap ((),) projr $ first' (introduce () :: p () ())

initial :: forall p a. Profunctor p => Unital (->) Void Void () p => p Void a
initial = rmap absurd $ introduce ()

poly :: forall p a b. Profunctor p => Unital (->) () Void () p => p a b
poly = dimap (const ()) absurd $ introduce ()

mono :: forall p. Unital (->) Void () () p => p Void ()
mono = introduce ()

split' :: a -> (a, a)
split' = split @(->) @(,)

merge' :: Either a a -> a
merge' = merge @(->) @Either

bipure :: (Bifunctor p, Unital (->) () () () p) => a -> b -> p a b 
bipure a b = bimap (const a) (const b) $ introduce @_ @() @() ()

biliftA2 :: (Bifunctor m, Semigroupal (->) (,) (,) (,) m) => (a -> b -> c) -> (d -> e -> f) -> m a d -> m b e -> m c f
biliftA2 f g m1 m2 = bimap (uncurry f) (uncurry g) $ combine (m1, m2)

biapply :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p (a -> b) (c -> d) -> p a c -> p b d
biapply = fmap (bimap (uncurry ($)) (uncurry ($))) . mux

infixl 4 <<*>>

(<<*>>) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p (a -> b) (c -> d) -> p a c -> p b d 
(<<*>>) = biapply

infixl 4 *>>

(*>>) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p c d
(*>>) = biliftA2 (const id) (const id)

infixl 4 <<*

(<<*) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p a b
(<<*) = biliftA2 const const
