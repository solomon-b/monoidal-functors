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

-- $setup
-- >>> :set -dppr-cols=1000
-- >>> import Prelude
-- >>> import Data.Void (Void)
-- >>> import Data.Tagged (Tagged (..), unTagged)
-- >>> import Data.Profunctor (Star (..), Forget (..))
-- >>> let evens = Star (\n -> if even n then Just n else Nothing) :: Star Maybe Int Int
-- >>> let positives = Star (\n -> if n > 0 then Just n else Nothing) :: Star Maybe Int Int
-- >>> let checker = Forget (\e -> Just (either negate (\b -> if b then 1 else 0) e)) :: Forget (Maybe Int) (Either Int Bool) (Either () ())
-- >>> let idForget = Forget Just :: Forget (Maybe Int) Int (Either () ())

--------------------------------------------------------------------------------

-- | Split the input between the two arguments and multiply their outputs.
--
-- ==== __Examples__
--
-- >>> mux (show :: Int -> String) not (123, False)
-- ("123",True)
mux :: (Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p (a, c) (b, d)
mux = curry combine

infixr 3 ***

-- | Infix operator for 'mux'.
--
-- ==== __Examples__
--
-- >>> ((show :: Int -> String) *** not) (123, False)
-- ("123",True)
(***) :: (Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p (a, c) (b, d)
(***) = mux

-- | Split the input between the two arguments and sum their outputs.
--
-- ==== __Examples__
--
-- >>> demux (show :: Int -> String) not (Left 5 :: Either Int Bool)
-- Left "5"
--
-- >>> demux (show :: Int -> String) not (Right True :: Either Int Bool)
-- Right False
demux :: (Semigroupal (->) Either Either (,) p) => p a b -> p c d -> p (Either a c) (Either b d)
demux = curry combine

infixr 2 +++

-- | Infix operator for 'demux'.
--
-- ==== __Examples__
--
-- >>> ((show :: Int -> String) +++ not) (Left 5 :: Either Int Bool)
-- Left "5"
(+++) :: (Semigroupal (->) Either Either (,) p) => p a b -> p c d -> p (Either a c) (Either b d)
(+++) = demux

-- | Send the whole input to the two arguments and multiply their outputs.
--
-- ==== __Examples__
--
-- >>> fanout (show :: Int -> String) even (4 :: Int)
-- ("4",True)
fanout :: (Profunctor p, Semigroupal (->) (,) (,) (,) p) => p x a -> p x b -> p x (a, b)
fanout pxa pxb = lmap split' $ pxa *** pxb

infixr 3 &&&

-- | Infix operator for 'fanout'.
--
-- ==== __Examples__
--
-- >>> ((show :: Int -> String) &&& even) (4 :: Int)
-- ("4",True)
(&&&) :: (Profunctor p, Semigroupal (->) (,) (,) (,) p) => p x a -> p x b -> p x (a, b)
(&&&) = fanout

-- | Split the input between the two arguments and merge their outputs.
--
-- ==== __Examples__
--
-- >>> fanin (show :: Int -> String) (show :: Bool -> String) (Left 5 :: Either Int Bool)
-- "5"
--
-- >>> fanin (show :: Int -> String) (show :: Bool -> String) (Right True :: Either Int Bool)
-- "True"
fanin :: (Profunctor p, Semigroupal (->) Either Either (,) p) => p a x -> p b x -> p (Either a b) x
fanin pax pbx = rmap merge' $ pax +++ pbx

infixr 2 |||

-- | Infix operator for 'fanin'.
--
-- ==== __Examples__
--
-- >>> ((show :: Int -> String) ||| (show :: Bool -> String)) (Left 5 :: Either Int Bool)
-- "5"
(|||) :: (Profunctor p, Semigroupal (->) Either Either (,) p) => p a x -> p b x -> p (Either a b) x
(|||) = fanin

-- | Split the input between the two arguments and sum their outputs.
--
-- Demonstrated on @'Star' 'Maybe'@, a parser-like profunctor. @evens@ succeeds on
-- even inputs and @positives@ on positive ones.
--
-- ==== __Examples__
--
-- >>> runStar (switch evens positives) (4, 5)
-- Just (Left 4)
--
-- >>> runStar (switch evens positives) (5, 5)
-- Just (Right 5)
switch :: (Semigroupal (->) (,) Either (,) p) => p a b -> p c d -> p (a, c) (Either b d)
switch = curry combine

infixr 5 &|

-- | Infix operator for 'switch'.
--
-- ==== __Examples__
--
-- >>> runStar (evens &| positives) (5, 5)
-- Just (Right 5)
(&|) :: (Semigroupal (->) (,) Either (,) p) => p a b -> p c d -> p (a, c) (Either b d)
(&|) = switch

-- | Send the whole input to the two arguments and sum their outputs.
--
-- ==== __Examples__
--
-- >>> runStar (union evens positives) 4
-- Just (Left 4)
union :: (Profunctor p) => (Semigroupal (->) (,) Either (,) p) => p x a -> p x b -> p x (Either a b)
union pxa pxb = lmap split' $ pxa &| pxb

-- | Split the input between the two arguments then merge their outputs.
--
-- ==== __Examples__
--
-- >>> runStar (divide evens positives) (4, 5)
-- Just 4
divide :: (Profunctor p, Semigroupal (->) (,) Either (,) p) => p a x -> p b x -> p (a, b) x
divide pxa pxb = rmap merge' $ pxa &| pxb

-- | Split the input between the two arguments then multiply their outputs.
--
-- ==== __Examples__
--
-- >>> splice (Right True :: Either Int Bool) (Right (7 :: Int) :: Either Int Int)
-- Right (True,7)
splice :: (Semigroupal (->) Either (,) (,) p) => p a b -> p c d -> p (Either a c) (b, d)
splice = curry combine

infix 5 |&

-- | Infix operator for 'splice'.
--
-- ==== __Examples__
--
-- >>> (Right True :: Either Int Bool) |& (Right (7 :: Int) :: Either Int Int)
-- Right (True,7)
(|&) :: (Semigroupal (->) Either (,) (,) p) => p a b -> p c d -> p (Either a c) (b, d)
(|&) = splice

-- | Route a choice of two profunctors to a profunctor over sums.
--
-- ==== __Examples__
--
-- >>> runStar (diverge (Left evens :: Either (Star Maybe Int Int) (Star Maybe Int Int))) (Left 4)
-- Just (Left 4)
diverge :: (Semigroupal (->) Either Either Either p) => Either (p a b) (p c d) -> p (Either a c) (Either b d)
diverge = combine

-- | Precompose a profunctor with a partial function, discarding 'Nothing's.
--
-- ==== __Examples__
--
-- >>> runStar (contramapMaybe (\x -> if x > 10 then Just x else Nothing) evens) 12
-- Just 12
contramapMaybe :: (Profunctor p) => (Semigroupal (->) Either Either Either p) => (a -> Maybe b) -> p b x -> p a x
contramapMaybe f = dimap (maybe (Right ()) Left . f) merge' . ultraleft

-- | Combine a choice of profunctors sharing an input, tensoring their outputs.
--
-- ==== __Examples__
--
-- >>> (zig (Left (show :: Int -> String)) :: Int -> Either String ()) 5
-- Left "5"
zig :: (Profunctor p, Semigroupal (->) (,) t Either p) => Either (p x a) (p x b) -> p x (t a b)
zig = lmap split' . combine

-- | Combine a choice of profunctors sharing an output, tensoring their inputs.
--
-- ==== __Examples__
--
-- >>> (zag (Left (show :: Int -> String)) :: (Int, ()) -> String) (5, ())
-- "5"
zag :: (Profunctor p, Semigroupal (->) t Either Either p) => Either (p a x) (p b x) -> p (t a b) x
zag = rmap merge' . combine

ultrafirst :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (a, x) (b, y)
ultrafirst = zag . Left . zig . Left

ultrasecond :: (Profunctor p, Semigroupal (->) (,) (,) Either p) => p a b -> p (x, a) (y, b)
ultrasecond = zag . Right . zig . Right

-- | Widen a profunctor's input and output on the left of a sum.
--
-- ==== __Examples__
--
-- >>> runStar (ultraleft evens) (Left 4 :: Either Int Int)
-- Just (Left 4)
ultraleft :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either a x) (Either b y)
ultraleft = zag . Left . zig . Left

-- | Widen a profunctor's input and output on the right of a sum.
--
-- ==== __Examples__
--
-- >>> runStar (ultraright evens) (Right 4 :: Either Int Int)
-- Just (Right 4)
ultraright :: (Profunctor p, Semigroupal (->) Either Either Either p) => p a b -> p (Either x a) (Either y b)
ultraright = zag . Right . zig . Right

-- | Split a bifunctor over a product into its two factors.
--
-- ==== __Examples__
--
-- >>> comux ((1, 2), (3, 4)) :: ((Int, Int), (Int, Int))
-- ((1,3),(2,4))
comux :: forall p a b c d. (Semigroupal Op (,) (,) (,) p) => p (a, c) (b, d) -> (p a b, p c d)
comux = getOp combine

-- | Split a profunctor over a product input into its two factors.
--
-- ==== __Examples__
--
-- >>> unTagged (fst (undivide (Tagged 42 :: Tagged (Int, Bool) Int)))
-- 42
undivide :: forall p x a b. (Profunctor p) => (Semigroupal Op (,) (,) (,) p) => p (a, b) x -> (p a x, p b x)
undivide = comux . rmap split'

-- | Split a profunctor over a sum on both sides into its two factors.
--
-- ==== __Examples__
--
-- >>> runForget (fst (codemux checker)) 5
-- Just (-5)
codemux :: forall p a b c d. (Semigroupal Op Either Either (,) p) => p (Either a c) (Either b d) -> (p a b, p c d)
codemux = getOp combine

-- | Split a profunctor over a sum output into its two branches.
--
-- ==== __Examples__
--
-- >>> runForget (fst (partition idForget)) 5
-- Just 5
partition :: forall p x a b. (Profunctor p) => (Semigroupal Op Either Either (,) p) => p x (Either a b) -> (p x a, p x b)
partition = codemux . lmap merge'

coswitch :: forall p a b c d. (Semigroupal Op Either (,) (,) p) => p (Either a c) (b, d) -> (p a b, p c d)
coswitch = getOp combine

unfanin :: forall p x a b. (Profunctor p) => (Semigroupal Op Either (,) (,) p) => p (Either a b) x -> (p a x, p b x)
unfanin = coswitch . rmap split'

unzip :: forall p x a b. (Profunctor p) => (Semigroupal Op Either (,) (,) p) => p x (a, b) -> (p x a, p x b)
unzip = coswitch . lmap merge'

cosplice :: forall p a b c d. (Semigroupal Op (,) Either (,) p) => p (a, c) (Either b d) -> (p a b, p c d)
cosplice = getOp combine

-- | The unique morphism into the terminal object @()@.
--
-- ==== __Examples__
--
-- >>> terminal (5 :: Int)
-- ()
terminal :: forall p a. (Profunctor p) => (Unital (->) () () () p) => p a ()
terminal = lmap (const ()) $ introduce ()

-- | The reflexive morphism of a 'Strong', 'Unital' profunctor.
--
-- ==== __Examples__
--
-- >>> ppure (5 :: Int)
-- 5
ppure :: forall p a. (Profunctor p) => (Unital (->) () () () p) => (Strong p) => p a a
ppure = dimap ((),) projr $ first' (introduce () :: p () ())

initial :: forall p a. (Profunctor p) => (Unital (->) Void Void () p) => p Void a
initial = rmap absurd $ introduce ()

-- | The empty profunctor, producing no output for any input.
--
-- ==== __Examples__
--
-- >>> runStar (poly :: Star Maybe Int Bool) 5
-- Nothing
poly :: forall p a b. (Profunctor p) => (Unital (->) () Void () p) => p a b
poly = dimap (const ()) absurd $ introduce ()

-- | The unique morphism from the initial object.
--
-- ==== __Examples__
--
-- >>> mono :: Either Void ()
-- Right ()
mono :: forall p. (Unital (->) Void () () p) => p Void ()
mono = introduce ()

-- | Duplicate a value into both components of a pair.
--
-- ==== __Examples__
--
-- >>> split' True
-- (True,True)
split' :: a -> (a, a)
split' = split @(->) @(,)

-- | Collapse a sum of a type with itself.
--
-- ==== __Examples__
--
-- >>> merge' (Left True :: Either Bool Bool)
-- True
merge' :: Either a a -> a
merge' = merge @(->) @Either

-- | Lift two values into a 'Unital' bifunctor.
--
-- ==== __Examples__
--
-- >>> bipure (0 :: Int) True :: (Int, Bool)
-- (0,True)
bipure :: (Bifunctor p, Unital (->) () () () p) => a -> b -> p a b
bipure a b = bimap (const a) (const b) $ introduce @_ @() @() ()

-- | Combine two bifunctors component-wise under a pair of binary functions.
--
-- ==== __Examples__
--
-- >>> biliftA2 (+) (\a b -> a && b) (1 :: Int, True) (3, False)
-- (4,False)
biliftA2 :: (Bifunctor m, Semigroupal (->) (,) (,) (,) m) => (a -> b -> c) -> (d -> e -> f) -> m a d -> m b e -> m c f
biliftA2 f g m1 m2 = bimap (uncurry f) (uncurry g) $ combine (m1, m2)

-- | Apply a bifunctor of functions to a bifunctor of arguments.
--
-- ==== __Examples__
--
-- >>> biapply (negate, not) (5 :: Int, True)
-- (-5,False)
biapply :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p (a -> b) (c -> d) -> p a c -> p b d
biapply = fmap (bimap (uncurry ($)) (uncurry ($))) . mux

infixl 4 <<*>>

-- | Infix operator for 'biapply'.
--
-- ==== __Examples__
--
-- >>> (negate, not) <<*>> (5 :: Int, True)
-- (-5,False)
(<<*>>) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p (a -> b) (c -> d) -> p a c -> p b d
(<<*>>) = biapply

infixl 4 *>>

-- | Sequence two bifunctors, keeping the outputs of the second.
--
-- ==== __Examples__
--
-- >>> (1 :: Int, True) *>> (3 :: Int, False)
-- (3,False)
(*>>) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p c d
(*>>) = biliftA2 (const id) (const id)

infixl 4 <<*

-- | Sequence two bifunctors, keeping the outputs of the first.
--
-- ==== __Examples__
--
-- >>> (1 :: Int, True) <<* (3 :: Int, False)
-- (1,True)
(<<*) :: (Bifunctor p, Semigroupal (->) (,) (,) (,) p) => p a b -> p c d -> p a b
(<<*) = biliftA2 const const
