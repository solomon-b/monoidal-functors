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
module Data.Functor.Categorical where

--------------------------------------------------------------------------------

import Control.Applicative qualified as Hask
import Control.Category
import Control.Category.Tensor (Iso (..))
import Control.Monad qualified as Hask
import Control.Monad.Reader qualified as Hask
import Control.Monad.State qualified as Hask
import Data.Bifunctor qualified as Hask
import Data.Bool (Bool)
import Data.Either (Either)
import Data.Function (($))
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

type Functor :: (from -> to) -> Constraint
class (Category (Dom f), Category (Cod f)) => Functor (f :: from -> to) where
  type Dom f :: from -> from -> Type
  type Cod f :: to -> to -> Type

  map :: Dom f a b -> Cod f (f a) (f b)

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

-- data Nat2 source target f f' f'' where
--   Nat2 :: (forall x y. target (f x y) (f' x y)) -> Nat2 source target f f' f''

-- instance (Category c1, Category c2, Category c3) => Category (Nat2 c1 c2 c3) where
--   id = Nat2 _

type FunctorOf :: Cat from -> Cat to -> (from -> to) -> Constraint
class (Functor f, dom ~ Dom f, cod ~ Cod f) => FunctorOf dom cod f

instance (Functor f, dom ~ Dom f, cod ~ Cod f) => FunctorOf dom cod f

type EndofunctorOf :: Cat ob -> (ob -> ob) -> Constraint
type EndofunctorOf cat = FunctorOf cat cat

--------------------------------------------------------------------------------

newtype FromFunctor f a = FromFunctor (f a)
  deriving newtype (Hask.Functor)

instance (Hask.Functor f) => Functor (FromFunctor f) where
  type Dom (FromFunctor f) = (->)
  type Cod (FromFunctor f) = (->)

  map :: (a -> b) -> FromFunctor f a -> FromFunctor f b
  map = Hask.fmap

fmap :: (FunctorOf (->) (->) f) => (a -> b) -> f a -> f b
fmap = map

deriving via (FromFunctor Identity) instance Functor Identity

deriving via (FromFunctor []) instance Functor []

deriving via (FromFunctor ((,) a)) instance Functor ((,) a)

deriving via (FromFunctor ((->) r)) instance Functor ((->) r)

deriving via (FromFunctor Maybe) instance Functor Maybe

deriving via (FromFunctor (Either e)) instance Functor (Either e)

--------------------------------------------------------------------------------

newtype FromContra f a = FromContra {getContra :: f a}
  deriving newtype (Hask.Contravariant)

instance (Hask.Contravariant f) => Functor (FromContra f) where
  type Dom (FromContra f) = Op
  type Cod (FromContra f) = (->)

  map :: Dom (FromContra f) a b -> Cod (FromContra f) ((FromContra f) a) ((FromContra f) b)
  map = Hask.contramap . getOp

contramap :: (FunctorOf Op (->) f) => (a -> b) -> f b -> f a
contramap = map . Op

deriving via (FromContra Predicate) instance Functor Predicate

--------------------------------------------------------------------------------

type (<->) :: Cat Type
type (<->) = Iso (->)

instance Functor Endo where
  type Dom Endo = (<->)
  type Cod Endo = (->)

  map :: (a <-> b) -> Endo a -> Endo b
  map Iso {..} (Endo f) = Endo (fwd . f . bwd)

invmap :: (FunctorOf (<->) (->) f) => (a -> b) -> (b -> a) -> f a -> f b
invmap f g = map (Iso f g)

--------------------------------------------------------------------------------

newtype FromBifunctor f a b = FromBifunctor (f a b)
  deriving newtype (Hask.Functor, Hask.Bifunctor)

instance (Hask.Bifunctor p, FunctorOf (->) (->) (p x)) => Functor (FromBifunctor p x) where
  type Dom (FromBifunctor p x) = (->)
  type Cod (FromBifunctor p x) = (->)

  map :: (a -> b) -> FromBifunctor p x a -> FromBifunctor p x b
  map f (FromBifunctor pab) = FromBifunctor (map f pab)

instance (Hask.Bifunctor p, forall x. FunctorOf (->) (->) (p x)) => Functor (FromBifunctor p) where
  type Dom (FromBifunctor p) = (->)
  type Cod (FromBifunctor p) = (Nat (->) (->))

  map :: (a -> b) -> (Nat (->) (->)) (FromBifunctor p a) (FromBifunctor p b)
  map f = Nat (\(FromBifunctor pax) -> FromBifunctor (Hask.first f pax))

first :: forall p a b. (FunctorOf (->) (Nat (->) (->)) p) => (a -> b) -> forall x. p a x -> p b x
first f = let (Nat f') = map f in f'

second :: (FunctorOf (->) (->) (p x)) => (a -> b) -> p x a -> p x b
second = fmap

bimap :: (FunctorOf (->) (->) (p a), FunctorOf (->) (Nat (->) (->)) p) => (a -> b) -> (c -> d) -> p a c -> p b d
bimap f g = first f . second g

-- deriving via (FromBifunctor (,)) instance Functor (,)

instance Functor (,) where
  type Dom (,) = (->)
  type Cod (,) = Nat (->) (->)

  map :: (a -> b) -> Nat (->) (->) ((,) a) ((,) b)
  map f = Nat (Hask.first f)

instance Functor Either where
  type Dom Either = (->)
  type Cod Either = Nat (->) (->)

  map :: (e -> e1) -> Nat (->) (->) (Either e) (Either e1)
  map f = Nat (Hask.first f)

--------------------------------------------------------------------------------

newtype FromProfunctor f a b = FromProfunctor (f a b)
  deriving newtype (Hask.Functor, Hask.Profunctor)

instance (Hask.Profunctor p, FunctorOf (->) (->) (p x)) => Functor (FromProfunctor p x) where
  type Dom (FromProfunctor p x) = (->)
  type Cod (FromProfunctor p x) = (->)

  map :: (a -> b) -> Cod (FromProfunctor p x) (FromProfunctor p x a) (FromProfunctor p x b)
  map f (FromProfunctor pxa) = FromProfunctor (map f pxa)

instance (Hask.Profunctor p) => Functor (FromProfunctor p) where
  type Dom (FromProfunctor p) = Op
  type Cod (FromProfunctor p) = (Nat (->) (->))

  map :: Op a b -> Nat (->) (->) ((FromProfunctor p) a) ((FromProfunctor p) b)
  map (Op f) = Nat (\(FromProfunctor pax) -> FromProfunctor (Hask.lmap f pax))

lmap :: forall p a b. (FunctorOf Op (Nat (->) (->)) p) => (a -> b) -> forall x. p b x -> p a x
lmap f = let (Nat f') = map @_ @_ @p (Op f) in f'

rmap :: (FunctorOf (->) (->) (f x)) => (a -> b) -> f x a -> f x b
rmap = fmap

dimap :: (FunctorOf Op (Nat (->) (->)) p, forall x. FunctorOf (->) (->) (p x)) => (a -> b) -> (c -> d) -> p b c -> p a d
dimap f g = lmap f . rmap g

instance Functor (->) where
  type Dom (->) = Op
  type Cod (->) = Nat (->) (->)

  map :: Op a b -> Nat (->) (->) ((->) a) ((->) b)
  map (Op f) = Nat (. f)

--------------------------------------------------------------------------------

newtype FromFilterable f a = FromFilterable (f a)
  deriving newtype (Hask.Functor, Hask.Filterable)

instance (Hask.Filterable f) => Functor (FromFilterable f) where
  type Dom (FromFilterable f) = (Hask.Star Maybe)
  type Cod (FromFilterable f) = (->)

  map :: Hask.Star Maybe a b -> FromFilterable f a -> FromFilterable f b
  map (Hask.Star f) (FromFilterable fa) = FromFilterable (Hask.mapMaybe f fa)

mapMaybe :: (FunctorOf (Hask.Star Maybe) (->) f) => (a -> Maybe b) -> f a -> f b
mapMaybe f = map (Hask.Star f)

catMaybes :: (FunctorOf (Hask.Star Maybe) (->) f) => f (Maybe a) -> f a
catMaybes = map (Hask.Star id)

filter :: (FunctorOf (Hask.Star Maybe) (->) f) => (a -> Bool) -> f a -> f a
filter f = map (Hask.Star (\a -> if f a then Just a else Nothing))

-- NOTE: These instances conflict with our Covariant Functor
-- instances. Switching from associated types to Multi Parameter type
-- classes would fix this:

-- deriving via (FromFilterable []) instance Functor []

-- deriving via (FromFilterable Maybe) instance Functor Maybe

--------------------------------------------------------------------------------

type Trifunctor :: (Type -> Type -> Type -> Type) -> Constraint
type Trifunctor = FunctorOf (->) (Nat (->) (Nat (->) (->)))

instance Functor (,,) where
  type Dom (,,) = (->)
  type Cod (,,) = (Nat (->) (Nat (->) (->)))

  map :: (a -> b) -> (Nat (->) (Nat (->) (->))) ((,,) a) ((,,) b)
  map f = Nat (Nat (\(x, y, z) -> (f x, y, z)))

instance Functor ((,,) x) where
  type Dom ((,,) x) = (->)
  type Cod ((,,) x) = Nat (->) (->)

  map :: (a -> b) -> Nat (->) (->) ((,,) x a) ((,,) x b)
  map f = Nat (\(x, y, z) -> (x, f y, z))

deriving via FromFunctor ((,,) x y) instance Functor ((,,) x y)

tripleFirst :: (a -> b) -> (a, x, y) -> (b, x, y)
tripleFirst f = let (Nat (Nat f')) = map f in f'

tripleSecond :: (a -> b) -> (x, a, z) -> (x, b, z)
tripleSecond f = let (Nat f') = map f in f'

tripleThird :: (a -> b) -> (x, y, a) -> (x, y, b)
tripleThird = map

newtype MealyM m s i o = MealyM {runMealyM :: s -> i -> m (o, s)}
  deriving
    (Hask.Functor, Hask.Applicative, Hask.Monad)
    via Hask.StateT s (Hask.ReaderT i m)

deriving via (FromFunctor (MealyM m s i)) instance (Hask.Functor m) => Functor (MealyM m s i)

instance (FunctorOf (->) (->) m) => Functor (MealyM m) where
  type Dom (MealyM m) = (<->)
  type Cod (MealyM m) = Nat Op (Nat (->) (->))

  map :: (a <-> b) -> Nat Op (Nat (->) (->)) (MealyM m a) (MealyM m b)
  map Iso {..} = Nat $ Nat $ \(MealyM mealy) -> MealyM $ \s i -> map (map fwd) $ mealy (bwd s) i

instance Functor (MealyM m s) where
  type Dom (MealyM m s) = Op
  type Cod (MealyM m s) = Nat (->) (->)

  map :: Op a b -> Nat (->) (->) (MealyM m s a) (MealyM m s b)
  map (Op f) = Nat $ \(MealyM mealy) -> MealyM $ \s -> mealy s . f

--------------------------------------------------------------------------------

data MyHKD f = MyHKD {one :: f Bool, two :: f ()}

instance Functor MyHKD where
  type Dom MyHKD = (Nat (->) (->))
  type Cod MyHKD = (->)

  map :: (Nat (->) (->)) f g -> MyHKD f -> MyHKD g
  map (Nat nat) MyHKD {..} = MyHKD (nat one) (nat two)

newtype MyHKD2 p = MyHKD2 {field :: p () Bool}

instance Functor MyHKD2 where
  type Dom MyHKD2 = (Nat (->) (Nat (->) (->)))
  type Cod MyHKD2 = (->)

  map :: Dom MyHKD2 p q -> MyHKD2 p -> MyHKD2 q
  map (Nat (Nat nat)) MyHKD2 {..} = MyHKD2 (nat field)
