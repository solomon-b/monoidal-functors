{-# LANGUAGE MonoLocalBinds #-}
module Control.Category.Tensor where

import Prelude hiding (id)
import Control.Applicative
import Control.Category (Category, id)
import Data.Biapplicative
import Data.Functor.Contravariant
import Data.Profunctor
import Data.These
import Data.Void

class (Category p, Category q) => GBifunctor p q r t | t r -> p q where
  gbimap :: a `p` b -> c `q` d -> (t a c) `r` (t b d)

instance GBifunctor (->) (->) (->) t => GBifunctor Op Op Op t where
  gbimap :: Op a b -> Op c d -> Op (t a c) (t b d)
  gbimap (Op f) (Op g) = Op $ gbimap f g

instance GBifunctor (->) (->) (->) (,) where
  gbimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
  gbimap f g = bimap f g

instance GBifunctor (->) (->) (->) (Either) where
  gbimap :: (a -> b) -> (c -> d) -> Either a c -> Either b d
  gbimap f g = bimap f g

instance GBifunctor (->) (->) (->) (These) where
  gbimap :: (a -> b) -> (c -> d) -> These a c -> These b d
  gbimap f g = bimap f g

instance GBifunctor (Star Maybe) (Star Maybe) (Star Maybe) These where
  gbimap :: Star Maybe a b -> Star Maybe c d -> Star Maybe (These a c) (These b d)
  gbimap (Star f) (Star g) =
    Star $ \case
      This a -> This <$> f a
      That c -> That <$> g c
      These a c -> liftA2 These (f a) (g c)

grmap :: GBifunctor p q r t => c `q` d -> (t a c) `r` (t a d)
grmap = gbimap id

glmap :: GBifunctor p q r t => a `p` b -> (t a c) `r` (t b c)
glmap = flip gbimap id

data Iso p a b = Iso { fwd :: a `p` b, bwd :: b `p` a }

class (Category p, GBifunctor p p p t) => Associative t p where
  assoc :: Iso p (t a (t b c)) (t (t a b) c)

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
    , bwd = either (either Left (Right . Left)) (Right . Right)
    }

instance Associative These (->) where
  assoc :: Iso (->) (These a (These b c)) (These (These a b) c)
  assoc = Iso
    { fwd = these (This . This) (glmap That) (glmap . These)
    , bwd = these (grmap This) (That . That) (flip $ grmap . flip These)
    }

class Associative t p => Tensor t i p | t -> i where
  lunit :: Iso p (t i a) a
  runit :: Iso p (t a i) a

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
    { fwd = these absurd id (flip const)
    , bwd = That
    }

  runit :: Iso (->) (These a Void) a
  runit = Iso
    { fwd = these id absurd const
    , bwd = This
    }

class Associative t p => Symmetric t p where
  swap :: (t a b) `p` (t b a)

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

class (Symmetric t p, Tensor t i p) => Cartesian t i p | i -> t, t -> i where
  diagonal :: a `p` (t a a)
  terminal :: a `p` i

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
