{-# LANGUAGE MonoLocalBinds #-}
module Control.Category.Tensor where

import           Control.Applicative
import           Control.Category           (Category, id)
import           Data.Biapplicative
import           Data.Functor.Contravariant
import           Data.Profunctor
import           Data.These
import           Data.Void
import           Prelude                    hiding (id)

{-

| Tensor | Unit |
+--------|------+
|  (,)   |  ()  |
| Either | Void |
| These  | Void |

tensor (or monoidal category) structure
  = category `cat`
  + bifunctor `t` on `cat`
  + unit object `i` in `cat`
  + isomorphisms in `cat`: `t i a <-> a`, `t a i <-> a`, `t a (t b c) <-> t (t a b) c`
  + some equational laws

lax monoidal functor = a functor that goes between the underlying
categories of two different monoidal structure, and has a pair of
operations `t2 (f a) (f b) -> f (t1 a b)` and `i2 -> f i1`

-}

data Iso cat a b = Iso { fwd :: cat a b, bwd :: cat b a }

-- Bifunctors
class (Category cat1, Category cat2, Category cat3) => GBifunctor cat1 cat2 cat3 t | t cat3 -> cat1 cat2 where
  gbimap :: cat1 a b -> cat2 c d -> cat3 (a `t` c)  (b `t` d)

  infixr 9 #
  (#) :: cat1 a b -> cat2 c d -> cat3 (a `t` c)  (b `t` d)
  (#) = gbimap
  {-# MINIMAL gbimap | (#) #-}


instance GBifunctor (->) (->) (->) t => GBifunctor Op Op Op t where
  gbimap :: Op a b -> Op c d -> Op (t a c) (t b d)
  gbimap (Op f) (Op g) = Op $ gbimap f g


instance Bifunctor t => GBifunctor (->) (->) (->) t where
  gbimap = bimap


instance GBifunctor (Star Maybe) (Star Maybe) (Star Maybe) These where
  gbimap :: Star Maybe a b -> Star Maybe c d -> Star Maybe (These a c) (These b d)
  gbimap (Star f) (Star g) =
    Star $ \case
      This a    -> This <$> f a
      That c    -> That <$> g c
      These a c -> liftA2 These (f a) (g c)


grmap :: GBifunctor cat1 cat2 cat3 t => cat2 c d -> cat3 (a `t` c) (a `t` d)
grmap = (#) id

glmap :: GBifunctor cat1 cat2 cat3 t => cat1 a b -> cat3 (a `t` c) (b `t` c)
glmap = flip (#) id


-- Associative Bifunctors
class (Category cat, GBifunctor cat cat cat t) => Associative cat t where
  assoc :: Iso cat (a `t` (b `t` c)) ((a `t` b) `t` c)


instance Associative (->) t => Associative Op t where
  assoc :: Iso Op (a `t` (b `t` c)) ((a `t` b) `t` c)
  assoc = Iso
    { fwd = Op $ bwd assoc
    , bwd = Op $ fwd assoc
    }


instance Associative (->) (,) where
  assoc :: Iso (->) (a, (b, c)) ((a, b), c)
  assoc = Iso
    { fwd = \(a, (b, c)) -> ((a, b), c)
    , bwd = \((a, b), c) -> (a, (b, c))
    }


instance Associative (->) Either where
  assoc :: Iso (->) (Either a (Either b c)) (Either (Either a b) c)
  assoc = Iso
    { fwd = either (Left . Left) (either (Left . Right) Right)
    , bwd = either (fmap Left) (Right . Right)
    }


instance Associative (->) These where
  assoc :: Iso (->) (These a (These b c)) (These (These a b) c)
  assoc = Iso
    { fwd = these (This . This) (glmap That) (glmap . These)
    , bwd = these (grmap This) (That . That) (flip $ grmap . flip These)
    }


instance (Monad m, Associative (->) t, GBifunctor (Star m) (Star m) (Star m) t) => Associative (Star m) t where
  assoc :: Iso (Star m) (a `t` (b `t` c)) ((a `t` b) `t` c)
  assoc = Iso
    { fwd = (`rmap` id) (fwd assoc)
    , bwd = (`rmap` id) (bwd assoc)
    }


-- Associative unital bifunctors
class Associative cat t => Tensor cat t i | t -> i where
  unitl :: Iso cat (i `t` a) a
  unitr :: Iso cat (a `t` i) a


instance (Tensor (->) t i) => Tensor Op t i where
  unitl :: Iso Op (i `t` a) a
  unitl = Iso
    { fwd = Op $ bwd unitl
    , bwd = Op $ fwd unitl
    }

  unitr :: Iso Op (a `t` i) a
  unitr = Iso
    { fwd = Op $ bwd unitr
    , bwd = Op $ fwd unitr
    }


instance Tensor (->) (,) () where
  unitl :: Iso (->) ((), a) a
  unitl = Iso
    { fwd = snd
    , bwd = bipure ()
    }

  unitr :: Iso (->) (a, ()) a
  unitr = Iso
    { fwd = fst
    , bwd = (`bipure` ())
    }


instance Tensor (->) Either Void where
  unitl :: Iso (->) (Either Void a) a
  unitl = Iso
     { fwd = either absurd id
     , bwd = pure
     }

  unitr :: Iso (->) (Either a Void) a
  unitr = Iso
    { fwd = either id absurd
    , bwd = Left
    }


instance Tensor (->) These Void where
  unitl :: Iso (->) (These Void a) a
  unitl = Iso
    { fwd = these absurd id (\ _ x -> x)
    , bwd = That
    }

  unitr :: Iso (->) (These a Void) a
  unitr = Iso
    { fwd = these id absurd const
    , bwd = This
    }


instance (Monad m, Tensor (->) t i, Associative (Star m) t) => Tensor (Star m) t i where
  unitl :: Iso (Star m) (i `t` a) a
  unitl = Iso
    { fwd = (`rmap` id) (fwd unitl)
    , bwd = (`rmap` id) (bwd unitl)
    }

  unitr :: Iso (Star m) (a `t` i) a
  unitr = Iso
    { fwd = (`rmap` id) (fwd unitr)
    , bwd = (`rmap` id) (bwd unitr)
    }


-- Symmetric bifunctors
class Associative cat t => Symmetric cat t where
  swap :: cat (a `t` b) (b `t` a)


instance (Symmetric (->) t) => Symmetric Op t where
  swap :: Op (a `t` b) (b `t` a)
  swap = Op swap


instance Symmetric (->) (,) where
  swap :: (a, b) -> (b, a)
  swap (a, b) = (b, a)


instance Symmetric (->) Either where
  swap :: Either a b -> Either b a
  swap = either Right Left


instance Symmetric (->) These where
  swap :: These a b -> These b a
  swap = these That This (flip These)


instance (Monad m, Symmetric (->) t, Associative (Star m) t) => Symmetric (Star m) t where
  swap :: Star m (a `t` b) (b `t` a)
  swap = Star $ pure . swap
