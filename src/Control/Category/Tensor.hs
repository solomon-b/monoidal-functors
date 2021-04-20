module Control.Category.Tensor where

import Prelude hiding (id)
import Control.Category (Category, id)
import Data.Bifunctor
import Data.Functor.Contravariant
import Data.These

class (Category p, Category q) => GBifunctor p q r t | t r -> p q where
  gbimap :: p a b -> q c d -> r (t a c) (t b d)

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

grmap :: GBifunctor p q r t => q c d -> r (t a c) (t a d)
grmap = gbimap id

glmap :: GBifunctor p q r t => p a b -> r (t a c) (t b c)
glmap = flip gbimap id

data Iso p a b = Iso { fwd :: p a b, bwd :: p b a }

class (Category p, GBifunctor p p p t) => Associative t p where
  assoc :: forall a b c. Iso p (t a (t b c)) (t (t a b) c)

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
