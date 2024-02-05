{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE StandaloneKindSignatures #-}

module Data.Functor.Traversable
  ( Traversable (..),
  )
where

--------------------------------------------------------------------------------

import Control.Monad.Identity (Identity (..))
import Data.Functor.Monoidal (Monoidal, Semigroupal (..), Unital (..))
import Data.Kind (Constraint, Type)
import GHC.Generics
import Kindly qualified
import Prelude hiding (Traversable (..))

--------------------------------------------------------------------------------

class Traversable hkd where
  sequence :: forall f. (Kindly.Functor (->) f, Monoidal (->) (,) () (,) () f) => hkd f -> f (hkd Identity)
  default sequence :: forall p. (Kindly.Functor (->) p, Monoidal (->) (,) () (,) () p, Generic (hkd p), Generic (hkd Identity), GTraversable p (Rep (hkd p)) (Rep (hkd Identity))) => hkd p -> p (hkd Identity)
  sequence = Kindly.fmap to . gsequence @p @(Rep (hkd p)) @(Rep (hkd Identity)) . from

type GTraversable :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Constraint
class GTraversable f g h where
  gsequence :: g x -> f (h x)

instance (Kindly.Functor (->) f, GTraversable f g h) => GTraversable f (M1 _1 _2 g) (M1 _1 _2 h) where
  gsequence :: M1 _1 _2 g x -> f (M1 _1 _2 h x)
  gsequence (M1 f) = Kindly.fmap M1 $ gsequence @f @g @h f

instance (Kindly.Functor (->) f) => GTraversable f (K1 _1 (f a)) (K1 _1 (Identity a)) where
  gsequence :: K1 _1 (f a) x -> f (K1 _1 (Identity a) x)
  gsequence (K1 f) = Kindly.fmap (K1 . Identity) f

instance (Kindly.Functor (->) f, Monoidal (->) (,) () (,) () f) => GTraversable f U1 U1 where
  gsequence :: U1 x -> f (U1 x)
  gsequence U1 = Kindly.fmap (const U1) $ introduce @_ @() ()

instance (Kindly.Functor (->) f, Monoidal (->) (,) () (,) () f, GTraversable f g1 h1, GTraversable f g2 h2) => GTraversable f (g1 :*: g2) (h1 :*: h2) where
  gsequence :: (:*:) g1 g2 x -> f ((:*:) h1 h2 x)
  gsequence (hkd1 :*: hkd2) = Kindly.fmap (uncurry (:*:)) $ combine @_ @(,) (gsequence hkd1, gsequence hkd2)
