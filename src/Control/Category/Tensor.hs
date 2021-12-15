{-# LANGUAGE MonoLocalBinds #-}
module Control.Category.Tensor where

import Prelude hiding ((.), id)
import Control.Applicative
import Control.Category
import Data.Biapplicative
import Data.Functor.Contravariant
import Data.Profunctor
import Data.These
import Data.Void

{-

| Tensor | Unit |
+--------|------+
| Either | Void |
|  (,)   |  ()  |
| These  | Void |

tensor = monoidal structure =
    category
  + bifunctor on that category `t`
  + unit object in that category `i`
  + isomorphisms in that category `t i a <-> a`, `t a i <-> a`, `t a (t b c) <-> t (t a b) c`
  + some equalities

monoidal functor = a functor that goes between the underlying
categories of two different monoidal structure, and has a pair of
operations `t2 (f a) (f b) -> f (t1 a b)` and `i2 -> f i1`

-}

-- | An invertible mapping between 'a' and 'b' in category 'cat'.
data Iso cat a b = Iso { fwd :: cat a b, bwd :: cat b a }

instance Category cat => Category (Iso cat) where
  id :: Iso cat a a
  id = Iso id id

  (.) :: Iso cat b c -> Iso cat a b -> Iso cat a c
  bc . ab = Iso (fwd bc . fwd ab) (bwd ab . bwd bc)

class (Category cat1, Category cat2) => GBifunctor cat1 cat2 r t | t r -> cat1 cat2 where
  gbimap :: a `cat1` b -> c `cat2` d -> t a c `r` t b d

instance GBifunctor (->) (->) (->) t => GBifunctor Op Op Op t where
  gbimap :: Op a b -> Op c d -> Op (t a c) (t b d)
  gbimap (Op f) (Op g) = Op $ gbimap f g

instance GBifunctor (->) (->) (->) (,) where
  gbimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
  gbimap f g = bimap f g

instance GBifunctor (->) (->) (->) Either where
  gbimap :: (a -> b) -> (c -> d) -> Either a c -> Either b d
  gbimap f g = bimap f g

instance GBifunctor (->) (->) (->) These where
  gbimap :: (a -> b) -> (c -> d) -> These a c -> These b d
  gbimap f g = bimap f g

instance GBifunctor (Star Maybe) (Star Maybe) (Star Maybe) These where
  gbimap :: Star Maybe a b -> Star Maybe c d -> Star Maybe (These a c) (These b d)
  gbimap (Star f) (Star g) =
    Star $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> liftA2 These (f a) (g c)

instance GBifunctor cat cat cat t => GBifunctor (Iso cat) (Iso cat) (Iso cat) t where
  gbimap :: Iso cat a b -> Iso cat c d -> Iso cat (t a c) (t b d)
  gbimap iso1 iso2 = Iso (gbimap (fwd iso1) (fwd iso2)) (gbimap (bwd iso1) (bwd iso2))

grmap :: GBifunctor cat1 cat2 r t => c `cat2` d -> t a c `r` t a d
grmap = gbimap id

glmap :: GBifunctor cat1 cat2 r t => a `cat1` b -> t a c `r` t b c
glmap = flip gbimap id

class (Category cat, GBifunctor cat cat cat t) => Associative t cat where
  assoc :: Iso cat (a `t` (b `t` c)) ((a `t` b) `t` c)

instance Associative t (->) => Associative t Op where
  assoc :: Iso Op (t a (t b c)) (t (t a b) c)
  assoc = Iso
    { fwd = Op $ bwd assoc
    , bwd = Op $ fwd assoc
    }

instance (Monad m, Associative t (->), GBifunctor (Star m) (Star m) (Star m) t) => Associative t (Star m) where
  assoc :: Iso (Star m) (t a (t b c)) (t (t a b) c)
  assoc = Iso
    { fwd = (`rmap` id) (fwd assoc)
    , bwd = (`rmap` id) (bwd assoc)
    }

instance Associative (,) (->) where
  assoc :: Iso (->) (a, (b, c)) ((a, b), c)
  assoc = Iso
    { fwd = \(a, (b, c)) -> ((a, b), c)
    , bwd = \((a, b), c) -> (a, (b, c))
    }

instance Associative Either (->) where
  assoc :: Iso (->) (Either a (Either b c)) (Either (Either a b) c)
  assoc = Iso
    { fwd = either (Left . Left) (either (Left . Right) Right)
    , bwd = either (fmap Left) (Right . Right)
    }

instance Associative These (->) where
  assoc :: Iso (->) (These a (These b c)) (These (These a b) c)
  assoc = Iso
    { fwd = these (This . This) (glmap That) (glmap . These)
    , bwd = these (grmap This) (That . That) (flip $ grmap . flip These)
    }

instance Associative t cat => Associative t (Iso cat) where
  assoc :: Iso (Iso cat) (t a (t b c)) (t (t a b) c)
  assoc = Iso
    { fwd = assoc -- Iso (fwd assoc) (bwd assoc)
    , bwd = Iso (bwd assoc) (fwd assoc)
    }

class Associative t cat => Tensor t i cat | t -> i where
  lunit :: Iso cat (t i a) a
  runit :: Iso cat (t a i) a

instance (Tensor t i (->)) => Tensor t i Op where
  lunit :: Iso Op (t i a) a
  lunit = Iso
    { fwd = Op $ bwd lunit
    , bwd = Op $ fwd lunit
    }

  runit :: Iso Op (t a i) a
  runit = Iso
    { fwd = Op $ bwd runit
    , bwd = Op $ fwd runit
    }

instance (Monad m, Tensor t i (->), Associative t (Star m)) => Tensor t i (Star m) where
  lunit :: Iso (Star m) (t i a) a
  lunit = Iso
    { fwd = (`rmap` id) (fwd lunit)
    , bwd = (`rmap` id) (bwd lunit)
    }

  runit = Iso
    { fwd = (`rmap` id) (fwd runit)
    , bwd = (`rmap` id) (bwd runit)
    }

instance Tensor (,) () (->) where
  lunit :: Iso (->) ((), a) a
  lunit = Iso
    { fwd = snd
    , bwd = bipure ()
    }

  runit :: Iso (->) (a, ()) a
  runit = Iso
    { fwd = fst
    , bwd = (`bipure` ())
    }

instance Tensor Either Void (->) where
  lunit :: Iso (->) (Either Void a) a
  lunit = Iso
     { fwd = either absurd id
     , bwd = pure
     }

  runit :: Iso (->) (Either a Void) a
  runit = Iso
    { fwd = either id absurd
    , bwd = Left
    }

instance Tensor These Void (->) where
  lunit :: Iso (->) (These Void a) a
  lunit = Iso
    { fwd = these absurd id (\ _ x -> x)
    , bwd = That
    }

  runit :: Iso (->) (These a Void) a
  runit = Iso
    { fwd = these id absurd const
    , bwd = This
    }

instance Tensor t i cat => Tensor t i (Iso cat) where
  lunit :: Iso (Iso cat) (t i a) a
  lunit = Iso
    { fwd = Iso (fwd lunit) (bwd lunit)
    , bwd = Iso (bwd lunit) (fwd lunit)
    }

  runit :: Iso (Iso cat) (t a i) a
  runit = Iso
    { fwd = Iso (fwd runit) (bwd runit)
    , bwd = Iso (bwd runit) (fwd runit)
    }

class Associative t cat => Symmetric t cat where
  swap :: t a b `cat` t b a

instance (Symmetric t (->)) => Symmetric t Op where
  swap :: Op (t a b) (t b a)
  swap = Op swap

instance (Monad m, Symmetric t (->), Associative t (Star m)) => Symmetric t (Star m) where
  swap :: Star m (t a b) (t b a)
  swap = Star $ pure . swap

instance Symmetric (,) (->) where
  swap :: (a, b) -> (b, a)
  swap (a, b) = (b, a)

instance Symmetric Either (->) where
  swap :: Either a b -> Either b a
  swap = either Right Left

instance Symmetric These (->) where
  swap :: These a b -> These b a
  swap = these That This (flip These)

instance Symmetric t cat => Symmetric t (Iso cat) where
  swap :: Iso cat (t a b) (t b a)
  swap = Iso
    { fwd = swap
    , bwd = swap
    }

class (Symmetric t cat, Tensor t i cat) => Cartesian t i cat | i -> t, t -> i where
  diagonal :: a `cat` t a a
  terminal :: a `cat` i

instance Cartesian (,) () (->) where
  diagonal :: a -> (a , a)
  diagonal = dup

  terminal :: a -> ()
  terminal = const ()

instance Cartesian Either Void Op where
  diagonal :: Op a (Either a a)
  diagonal = Op merge

  terminal :: Op a Void
  terminal = Op absurd

dup :: a -> (a, a)
dup a = (a, a)

merge :: Either a a -> a
merge = either id id
