{-# LANGUAGE MonoLocalBinds #-}
module Control.Category.Tensor
  ( -- * Iso
    Iso (..),

    -- * GBifunctor
    GBifunctor (..),
    (#),
    grmap,
    glmap,
    -- * Associative
    Associative (..),

    -- * Tensor
    Tensor (..),

    -- * Symmetric
    Symmetric (..),
  )
where

--------------------------------------------------------------------------------

import Control.Applicative (Applicative (..))
import Control.Category (Category (..))
import Data.Biapplicative (Biapplicative (..), Bifunctor (..))
import Data.Functor.Contravariant (Op (..))
import Data.Profunctor (Profunctor (..), Star (..))
import Data.These (These (..), these)
import Data.Void (Void, absurd)
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

-- | An invertible mapping between 'a' and 'b' in category 'cat'.
--
-- === Laws
--
-- @
-- fwd ∘ bwd ≡ id
-- bwd ∘ fwd ≡ id
-- @
data Iso cat a b = Iso { fwd :: cat a b, bwd :: cat b a }

instance Category cat => Category (Iso cat) where
  id :: Iso cat a a
  id = Iso id id

  (.) :: Iso cat b c -> Iso cat a b -> Iso cat a c
  bc . ab = Iso (fwd bc . fwd ab) (bwd ab . bwd bc)

--------------------------------------------------------------------------------

-- | A Bifunctor @t@ is a binary type operator which allows you to map
-- over both variables. GBifunctor is the same as the ordinary
-- 'Data.Bifunctor.Bifunctor' class but we replace the '(->)'s with three different
-- higher kinded variables @cat1@, @cat2@, and @cat3@.
--
-- === Laws
--
-- @
-- gbimap id id ≡ id
-- grmap id ≡ id
-- glmap id ≡ id
--
-- gbimap (f ∘ g) (h ∘ i) ≡ gbimap f h ∘ gbimap g i
-- grmap (f ∘ g) ≡ grmap f ∘ grmap g
-- glmap (f ∘ g) ≡ glmap f ∘ glmap g
-- @
class (Category cat1, Category cat2, Category cat3) => GBifunctor cat1 cat2 cat3 t | t cat3 -> cat1 cat2 where
  -- | Map over both arguments at the same time.
  --
  -- @'gbimap' f g ≡ 'glmap' f '.' 'grmap' g@
  --
  -- ==== __Examples__
  -- >>> gbimap @(->) @(->) @(->) @(,) show not (123, False)
  -- ("123",True)
  --
  -- >>> gbimap @(->) @(->) @(->) @Either show not (Right False)
  -- Right True
  --
  -- >>> getOp (gbimap @Op @Op @Op @Either (Op (+ 1)) (Op show)) (Right True)
  -- Right "True"
  gbimap :: cat1 a b -> cat2 c d -> cat3 (a `t` c)  (b `t` d)

infixr 9 #
(#) :: GBifunctor cat1 cat2 cat3 t => cat1 a b -> cat2 c d -> cat3 (a `t` c)  (b `t` d)
(#) = gbimap

grmap :: GBifunctor cat1 cat2 cat3 t => cat2 c d -> cat3 (a `t` c) (a `t` d)
grmap = (#) id

glmap :: GBifunctor cat1 cat2 cat3 t => cat1 a b -> cat3 (a `t` c) (b `t` c)
glmap = flip (#) id

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

instance GBifunctor cat cat cat t => GBifunctor (Iso cat) (Iso cat) (Iso cat) t where
  gbimap :: Iso cat a b -> Iso cat c d -> Iso cat (t a c) (t b d)
  gbimap iso1 iso2 = Iso (gbimap (fwd iso1) (fwd iso2)) (gbimap (bwd iso1) (bwd iso2))

--------------------------------------------------------------------------------

-- | A binary type operator that is 'Associative' up to ismorphism.
--
-- === Laws
--
-- @
-- assoc.fwd ∘ assoc.bwd ≡ id
-- assoc.bwd ∘ assoc.fwd ≡ id
-- @
class (Category cat, GBifunctor cat cat cat t) => Associative cat t where
  -- | An 'Iso' that instantiates the isomorphism between left and
  -- right associated nesting of @t@.
  --
  -- ==== __Examples__
  --
  -- >>> :t assoc @(->) @(,) 
  -- assoc @(->) @(,) :: Iso (->) (a, (b, c)) ((a, b), c)
  --
  -- >>> fwd (assoc @(->) @(,)) (1, ("hello", True))
  -- ((1,"hello"),True)
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

--------------------------------------------------------------------------------

-- | A 'Associative' type operator @t@ is a 'Tensor' if it has a
-- corresponding identity type @i@ such the following laws are
-- respected:
--
-- === Laws
--
-- @
-- unitr.fwd (a ⊗ i) ≡ a
-- unitr.bwd a ≡ (a ⊗ i)
--
-- unitl.fwd (i ⊗ a) ≡ a 
-- unitl.bwd a ≡ (i ⊗ a)
-- @
class Associative cat t => Tensor cat t i | t -> i where
  -- | An 'Iso' that instantiates the isomorphism between @(i \`t\` a)@ and @a@.
  --
  -- ==== __Examples__
  --
  -- >>> fwd (unitl @_ @(,)) ((), True)
  -- True
  -- 
  -- >>> bwd (unitl @_ @(,)) True
  -- ((),True)
  --
  -- >>> bwd (unitl @_ @Either) True
  -- Right True
  --
  -- >>> :t bwd (unitl @_ @Either) True
  -- bwd (unitl @_ @Either) True :: Either Void Bool
  unitl :: Iso cat (i `t` a) a
  -- | An 'Iso' that instantiates the isomorphism between @(a \`t\` i)@ and @a@.
  --
  -- ==== __Examples__
  --
  -- >>> fwd (unitr @_ @(,)) (True, ())
  -- True
  -- 
  -- >>> bwd (unitr @_ @(,)) True
  -- (True,())
  --
  -- >>> bwd (unitr @_ @Either) True
  -- Left True
  --
  -- >>> :t bwd (unitr @_ @Either) True
  -- bwd (unitr @_ @Either) True :: Either Bool Void
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

--------------------------------------------------------------------------------

-- | A 'Associative' type operator @t@ is 'Symmetric' if it is commutative
-- up to isomorphism.
--
-- === Laws
--
-- @
-- swap ∘ swap ≡ id
-- @
class Associative cat t => Symmetric cat t where
  -- | @swap@ is a symmetry isomorphism for @t@
  --
  -- ==== __Examples__
  --
  -- >>> :t swap @(->) @(,)
  -- swap @(->) @(,) :: (a, b) -> (b, a)
  --
  -- >>> swap @(->) @(,) (True, "hello")
  -- ("hello",True)
  --
  -- >>> :t swap @(->) @Either (Left True)
  -- swap @(->) @Either (Left True) :: Either b Bool
  --
  -- >>> swap @(->) @Either (Left True)
  -- Right True
  swap :: cat (a `t` b) (b `t` a)


instance Symmetric (->) t => Symmetric Op t where
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
