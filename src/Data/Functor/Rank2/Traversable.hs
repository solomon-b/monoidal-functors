{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}

-- | Rank-2 traversal for higher-kinded data interpreted by a functor: the
-- analogue of "Data.Traversable" one level up. Generalizes @barbies@'
-- @TraversableB@ across the variance of the interpretation functor, so it
-- covers both covariant (@Applicative@) and contravariant (@Divisible@)
-- interpretations.
module Data.Functor.Rank2.Traversable
  ( Traversable (..),
  )
where

--------------------------------------------------------------------------------

import Control.Monad.Identity (Identity (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Isomorphism (Iso (..))
import Data.Kind (Constraint, Type)
import GHC.Generics
import Kindly qualified
import Prelude hiding (Traversable (..))

--------------------------------------------------------------------------------

-- | Higher-kinded data that distributes over any functor 'Monoidal' with
-- respect to tupling. The interpretation @f@ may have either variance,
-- selected by @cat@. At a covariant functor (@cat ~ (->)@) this is the
-- monoidal presentation of @Applicative@, as in @barbies@. At a contravariant
-- functor (@cat ~ Op@) it is @Divisible@, folding a record of @f@-consumers
-- into one consumer of the whole record.
--
-- The generic default covers records whose fields all have the shape @f a@.
-- Sums and nested HKD fields are not supported.
class Traversable hkd where
  -- | Pull the interpretation functor out of the record.
  sequence :: forall cat f. (Kindly.Functor cat f, Kindly.LiftIso cat, Monoidal (->) (,) () (,) () f) => hkd f -> f (hkd Identity)
  default sequence :: forall cat p. (Kindly.Functor cat p, Kindly.LiftIso cat, Monoidal (->) (,) () (,) () p, Generic (hkd p), Generic (hkd Identity), GTraversable p (Rep (hkd p)) (Rep (hkd Identity))) => hkd p -> p (hkd Identity)
  sequence = Kindly.mapIso (Iso to from) . gsequence @p @(Rep (hkd p)) @(Rep (hkd Identity)) . from

type GTraversable :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GTraversable f g h where
  gsequence :: g x -> f (h x)

instance (Kindly.Functor cat f, Kindly.LiftIso cat, GTraversable f g h) => GTraversable f (M1 _1 _2 g) (M1 _1 _2 h) where
  gsequence :: M1 _1 _2 g x -> f (M1 _1 _2 h x)
  gsequence (M1 f) = Kindly.mapIso (Iso M1 unM1) $ gsequence @f @g @h f

instance (Kindly.Functor cat f, Kindly.LiftIso cat) => GTraversable f (K1 _1 (f a)) (K1 _1 (Identity a)) where
  gsequence :: K1 _1 (f a) x -> f (K1 _1 (Identity a) x)
  gsequence (K1 f) = Kindly.mapIso (Iso (K1 . Identity) (runIdentity . unK1)) f

instance (Kindly.Functor cat f, Kindly.LiftIso cat, Monoidal (->) (,) () (,) () f) => GTraversable f U1 U1 where
  gsequence :: U1 x -> f (U1 x)
  gsequence U1 = Kindly.mapIso (Iso (const U1) (const ())) $ introduce @_ @() ()

instance (Kindly.Functor cat f, Kindly.LiftIso cat, Monoidal (->) (,) () (,) () f, GTraversable f g1 h1, GTraversable f g2 h2) => GTraversable f (g1 :*: g2) (h1 :*: h2) where
  gsequence :: (:*:) g1 g2 x -> f ((:*:) h1 h2 x)
  gsequence (hkd1 :*: hkd2) = Kindly.mapIso (Iso (uncurry (:*:)) (\(x :*: y) -> (x, y))) $ combine @_ @(,) (gsequence hkd1, gsequence hkd2)
