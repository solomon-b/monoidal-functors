{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}

-- | A scratchpad for implementing Iceland Jack and Ed Kmett's
-- categorical functor ideas.
--
-- If possible, this ought to give us a kind generic functor to
-- replace 'GBifunctor'.
--
-- We also ought to be able to use the same tricks to get a kind
-- generic Monoidal Functor class.
module Data.Functor.CategoricalV2 where

--------------------------------------------------------------------------------

import Control.Category
import Control.Category.Tensor (Iso (..))
import Control.Monad qualified as Hask
import Data.Bifunctor qualified as Hask
import Data.Bool (Bool)
import Data.Either (Either)
import Data.Functor.Contravariant (Op (..), Predicate (..))
import Data.Functor.Contravariant qualified as Hask
import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.Maybe (Maybe (..))
import Data.Monoid (Endo (..))
import Data.Profunctor qualified as Hask
import Data.Semigroupoid
import Witherable qualified as Hask

--------------------------------------------------------------------------------

class (Category dom, Category cod) => Functor (dom :: from -> from -> Type) (cod :: to -> to -> Type) (f :: from -> to) where
  map :: dom a b -> cod (f a) (f b)

type Cat i = i -> i -> Type

type Nat :: Cat s -> Cat t -> Cat (s -> t)
data Nat source target f f' where
  Nat :: (forall x. target (f x) (f' x)) -> Nat source target f f'

instance (Semigroupoid c1, Semigroupoid c2) => Semigroupoid (Nat c1 c2) where
  o :: Nat c1 c2 j k1 -> Nat c1 c2 i j -> Nat c1 c2 i k1
  Nat c1 `o` Nat c2 = Nat (c1 `o` c2)

instance (Semigroupoid c1, Semigroupoid c2, Category c1, Category c2) => Category (Nat c1 c2) where
  id :: Nat c1 c2 a a
  id = Nat id

  (.) = o

type Endofunctor :: Cat ob -> (ob -> ob) -> Constraint
type Endofunctor cat = Functor cat cat

--------------------------------------------------------------------------------

newtype FromFunctor f a = FromFunctor (f a)
  deriving newtype (Hask.Functor)

instance (Hask.Functor f) => Functor (->) (->) (FromFunctor f) where
  map :: (a -> b) -> FromFunctor f a -> FromFunctor f b
  map = Hask.fmap

fmap :: (Functor (->) (->) f) => (a -> b) -> f a -> f b
fmap = map

deriving via (FromFunctor Identity) instance Functor (->) (->) Identity

deriving via (FromFunctor []) instance Functor (->) (->) []

deriving via (FromFunctor ((,) a)) instance Functor (->) (->) ((,) a)

deriving via (FromFunctor ((->) r)) instance Functor (->) (->) ((->) r)

deriving via (FromFunctor Maybe) instance Functor (->) (->) Maybe

deriving via (FromFunctor (Either e)) instance Functor (->) (->) (Either e)

--------------------------------------------------------------------------------

newtype FromContra f a = FromContra {getContra :: f a}
  deriving newtype (Hask.Contravariant)

instance (Hask.Contravariant f) => Functor Op (->) (FromContra f) where
  map :: Op a b -> (FromContra f) a -> (FromContra f) b
  map = Hask.contramap . getOp

contramap :: (Functor Op (->) f) => (a -> b) -> f b -> f a
contramap = map . Op

deriving via (FromContra Predicate) instance Functor Op (->) Predicate

--------------------------------------------------------------------------------

type (<->) :: Cat Type
type (<->) = Iso (->)

instance Functor (<->) (->) Endo where
  map :: (a <-> b) -> Endo a -> Endo b
  map Iso {..} (Endo f) = Endo (fwd . f . bwd)

invmap :: (Functor (<->) (->) f) => (a -> b) -> (b -> a) -> f a -> f b
invmap f g = map (Iso f g)

--------------------------------------------------------------------------------

newtype FromBifunctor f a b = FromBifunctor (f a b)
  deriving newtype (Hask.Functor, Hask.Bifunctor)

instance (Hask.Bifunctor p, Functor (->) (->) (p x)) => Functor (->) (->) (FromBifunctor p x) where
  map :: (a -> b) -> FromBifunctor p x a -> FromBifunctor p x b
  map f (FromBifunctor pab) = FromBifunctor (map f pab)

instance (Hask.Bifunctor p, forall x. Functor (->) (->) (p x)) => Functor (->) (Nat (->) (->)) (FromBifunctor p) where
  map :: (a -> b) -> (Nat (->) (->)) (FromBifunctor p a) (FromBifunctor p b)
  map f = Nat (\(FromBifunctor pax) -> FromBifunctor (Hask.first f pax))

first :: forall p a b. (Functor (->) (Nat (->) (->)) p) => (a -> b) -> forall x. p a x -> p b x
first f = let (Nat f') = (map :: (a -> b) -> Nat (->) (->) (p a) (p b)) f in f'

second :: (Functor (->) (->) (p x)) => (a -> b) -> p x a -> p x b
second = fmap

bimap :: (Functor (->) (->) (p a), Functor (->) (Nat (->) (->)) p) => (a -> b) -> (c -> d) -> p a c -> p b d
bimap f g = first f . second g

-- deriving via (FromBifunctor (,)) instance Functor (->) (Nat (->) (->)) (,)

instance Functor (->) (Nat (->) (->)) (,) where
  map :: (a -> b) -> Nat (->) (->) ((,) a) ((,) b)
  map f = Nat (Hask.first f)

instance Functor (->) (Nat (->) (->)) Either where
  map :: (e -> e1) -> Nat (->) (->) (Either e) (Either e1)
  map f = Nat (Hask.first f)

--------------------------------------------------------------------------------

newtype FromProfunctor f a b = FromProfunctor (f a b)
  deriving newtype (Hask.Functor, Hask.Profunctor)

instance (Hask.Profunctor p, Functor (->) (->) (p x)) => Functor (->) (->) (FromProfunctor p x) where
  map :: (a -> b) -> FromProfunctor p x a -> FromProfunctor p x b
  map f (FromProfunctor pxa) = FromProfunctor (map f pxa)

instance (Hask.Profunctor p) => Functor Op (Nat (->) (->)) (FromProfunctor p) where
  map :: Op a b -> Nat (->) (->) ((FromProfunctor p) a) ((FromProfunctor p) b)
  map (Op f) = Nat (\(FromProfunctor pax) -> FromProfunctor (Hask.lmap f pax))

lmap :: forall p a b. (Functor Op (Nat (->) (->)) p) => (a -> b) -> forall x. p b x -> p a x
lmap f = let (Nat f') = (map :: Op b a -> Nat (->) (->) (p b) (p a)) (Op f) in f'

rmap :: (Functor (->) (->) (f x)) => (a -> b) -> f x a -> f x b
rmap = fmap

dimap :: (Functor Op (Nat (->) (->)) p, forall x. Functor (->) (->) (p x)) => (a -> b) -> (c -> d) -> p b c -> p a d
dimap f g = lmap f . rmap g

instance Functor Op (Nat (->) (->)) (->) where
  map :: Op a b -> Nat (->) (->) ((->) a) ((->) b)
  map (Op f) = Nat (. f)

--------------------------------------------------------------------------------

newtype FromFilterable f a = FromFilterable (f a)
  deriving newtype (Hask.Functor, Hask.Filterable)

instance (Hask.Filterable f) => Functor (Hask.Star Maybe) (->) (FromFilterable f) where
  map :: Hask.Star Maybe a b -> FromFilterable f a -> FromFilterable f b
  map (Hask.Star f) (FromFilterable fa) = FromFilterable (Hask.mapMaybe f fa)

mapMaybe :: (Functor (Hask.Star Maybe) (->) f) => (a -> Maybe b) -> f a -> f b
mapMaybe f = map (Hask.Star f)

catMaybes :: (Functor (Hask.Star Maybe) (->) f) => f (Maybe a) -> f a
catMaybes = map (Hask.Star id)

filter :: (Functor (Hask.Star Maybe) (->) f) => (a -> Bool) -> f a -> f a
filter f = map (Hask.Star (\a -> if f a then Just a else Nothing))

deriving via (FromFilterable []) instance Functor (Hask.Star Maybe) (->) []

deriving via (FromFilterable Maybe) instance Functor (Hask.Star Maybe) (->) Maybe

--------------------------------------------------------------------------------
-- TODO:

type Trifunctor :: (Type -> Type -> Type -> Type) -> Constraint
type Trifunctor = Functor (->) (Nat (->) (Nat (->) (->)))

instance Functor (->) (Nat (->) (Nat (->) (->))) (,,) where
  map :: (a -> b) -> (Nat (->) (Nat (->) (->))) ((,,) a) ((,,) b)
  map f = Nat (Nat (\(x, y, z) -> (f x, y, z)))

instance Functor (->) (Nat (->) (->)) ((,,) x) where
  map :: (a -> b) -> Nat (->) (->) ((,,) x a) ((,,) x b)
  map f = Nat (\(x, y, z) -> (x, f y, z))

deriving via FromFunctor ((,,) x y) instance Functor (->) (->) ((,,) x y)

tripleFirst :: (a -> b) -> (a, x, y) -> (b, x, y)
tripleFirst f = let (Nat (Nat f')) = (map :: (a -> b) -> Nat (->) (Nat (->) (->)) ((,,) a) ((,,) b)) f in f'

tripleSecond :: (a -> b) -> (x, a, z) -> (x, b, z)
tripleSecond f = let (Nat f') = (map :: (a -> b) -> Nat (->) (->) ((,,) x a) ((,,) x b)) f in f'

tripleThird :: (a -> b) -> (x, y, a) -> (x, y, b)
tripleThird = map

-- newtype Mealy m s i o = Mealy { runMealy :: s -> i -> m (o, s) }
--   deriving
--     (Hask.Functor, Hask.Applicative, Hask.Monad)
--     via Hask.StateT s (Hask.ReaderT i m)

-- deriving via (FromFunctor (Mealy m s i)) instance (Hask.Functor m) => Functor (Mealy m s i)

-- instance Functor (Mealy m s) where
--   type Dom (Mealy m s) = Op
--   type Cod (Mealy m s) = Nat (->) (->)

--   map :: Dom (Mealy m s) a b -> Cod (Mealy m s) (Mealy m s a) (Mealy m s b)
--   map = _

--------------------------------------------------------------------------------

-- Some Ideal Interface
-- THIS IS ALL WRONG

class Map1 dom cod f | f -> cod, f -> dom where
  map1 :: dom a b -> cod (f a) (f b)

instance (Hask.Functor f) => Map1 (->) (->) (FromFunctor f) where
  map1 f (FromFunctor fa) = FromFunctor (Hask.fmap f fa)

instance (Hask.Contravariant f) => Map1 Op (->) (FromContra f) where
  map1 f (FromContra fa) = FromContra (Hask.contramap (getOp f) fa)

instance (Hask.Filterable f) => Map1 (Hask.Star Maybe) (->) (FromFilterable f) where
  map1 :: Hask.Star Maybe a b -> FromFilterable f a -> FromFilterable f b
  map1 (Hask.Star f) (FromFilterable fa) = FromFilterable (Hask.mapMaybe f fa)

instance (Hask.Bifunctor p) => Map1 (->) (->) (FromBifunctor p x) where
  map1 :: (a -> b) -> FromBifunctor p x a -> FromBifunctor p x b
  map1 f (FromBifunctor pab) = FromBifunctor (Hask.second f pab)

instance (Hask.Profunctor p) => Map1 (->) (->) (FromProfunctor p x) where
  map1 f (FromProfunctor pab) = FromProfunctor (Hask.rmap f pab)

class Map2 dom cod f where
  map2 :: dom a b -> cod (f a x) (f b x)

instance (Hask.Bifunctor p) => Map1 (->) (Nat (->) (->)) (FromBifunctor p) where
  map1 f = Nat (\(FromBifunctor pab) -> FromBifunctor (Hask.first f pab))

instance (Hask.Profunctor p) => Map1 Op (Nat (->) (->)) (FromProfunctor p) where
  map1 f = Nat (\(FromProfunctor pab) -> FromProfunctor (Hask.lmap (getOp f) pab))

class Map3 dom cod f where
  map3 :: dom a b -> cod (f a x y) (f b x y)
