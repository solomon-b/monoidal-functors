module Data.Bifunctor.Module where

import Data.Profunctor
import Data.Either (Either(..))
import Data.Functor.Contravariant (Contravariant, Op(..))
import Control.Category ((.))
import Control.Monad (Monad, Functor)
import Control.Arrow (Kleisli(..), Arrow, ArrowChoice)
import Data.Profunctor.Strong (Pastro, Tambara)
import Data.Profunctor.Closed (Closure)
import Data.Profunctor.Traversing (FreeTraversing, CofreeTraversing)
import Data.Profunctor.Mapping (FreeMapping, CofreeMapping)
import Data.Profunctor.Yoneda (Coyoneda, Yoneda)
import Data.Bifunctor.Clown (Clown)
import Data.Bifunctor.Sum (Sum)
import Data.Bifunctor.Product (Product)
import Data.Profunctor.Composition (Procompose)
import Data.Profunctor.Cayley (Cayley)
import Data.Tagged (Tagged)
import Data.Profunctor.Choice (PastroSum, TambaraSum)
import Control.Comonad (Cokleisli, Comonad)
import Data.Monoid (Monoid)
import Control.Applicative (Applicative)
import Data.Bifunctor.Joker (Joker)
import Data.Bifunctor.Tannen (Tannen)
import Data.Function (const)
import Control.Category.Tensor
import Data.Bifunctor
import Data.These (These)

newtype FromProfunctor p a b = FromProfunctor (p a b)

-----------------------------------------------------------------------
-- LeftModule

class LeftModule cat t1 t2 f where
  lstrength :: cat (f a b) (f (t1 a c) (t2 b c))

instance Strong p => LeftModule (->) (,) (,) (FromProfunctor p) where
  lstrength :: FromProfunctor p a b -> FromProfunctor p (a, c) (b, c)
  lstrength (FromProfunctor p) = FromProfunctor (first' p)

instance Choice p => LeftModule (->) Either Either (FromProfunctor p) where
  lstrength :: FromProfunctor p a b -> FromProfunctor p (Either a c) (Either b c)
  lstrength (FromProfunctor p) = FromProfunctor (left' p)

deriving via (FromProfunctor (Kleisli m)) instance Monad m => LeftModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor (Pastro p)) instance LeftModule (->) (,) (,) (Pastro p)
deriving via (FromProfunctor (Tambara p)) instance Profunctor p => LeftModule (->) (,) (,) (Tambara p)
deriving via (FromProfunctor (Closure p)) instance Strong p => LeftModule (->) (,) (,) (Closure p)
deriving via (FromProfunctor (FreeTraversing p)) instance LeftModule (->) (,) (,) (FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => LeftModule (->) (,) (,) (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p)) instance LeftModule (->) (,) (,) (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p)) instance Profunctor p => LeftModule (->) (,) (,) (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p)) instance Strong p => LeftModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Yoneda p)) instance Strong p => LeftModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->)) instance LeftModule (->) (,) (,) (->)
deriving via (FromProfunctor (Forget r)) instance LeftModule (->) (,) (,) (Forget r)
deriving via (FromProfunctor (Star m)) instance Functor m => LeftModule (->) (,) (,) (Star m)
deriving via (FromProfunctor (Clown f)) instance Contravariant f => LeftModule (->) (,) (,) (Clown f)
deriving via (FromProfunctor (WrappedArrow p)) instance Arrow p => LeftModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q)) instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q)) instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Procompose p q)) instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f q)) instance (Functor f, Strong q) => LeftModule (->) (,) (,) (Cayley f q)

deriving via (FromProfunctor (Kleisli m)) instance Monad m => LeftModule (->) Either Either (Kleisli m)
deriving via (FromProfunctor Tagged) instance LeftModule (->) Either Either Tagged
deriving via (FromProfunctor (Tambara p)) instance (Choice p) => LeftModule (->) Either Either (Tambara p)
deriving via (FromProfunctor (PastroSum p)) instance LeftModule (->) Either Either (PastroSum p)
deriving via (FromProfunctor (TambaraSum p)) instance Profunctor p => LeftModule (->) Either Either (TambaraSum p)
deriving via (FromProfunctor (FreeTraversing p)) instance LeftModule (->) Either Either ( FreeTraversing p) 
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => LeftModule (->) Either Either (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p )) instance LeftModule (->) Either Either (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p)) instance Profunctor p => LeftModule (->) Either Either (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p)) instance Choice p => LeftModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p)) instance Choice p => LeftModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->)) instance LeftModule (->) Either Either (->)
deriving via (FromProfunctor (Cokleisli w)) instance Comonad w => LeftModule (->) Either Either (Cokleisli w)
deriving via (FromProfunctor (Forget r)) instance Monoid r => LeftModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Star f)) instance Applicative f => LeftModule (->) Either Either (Star f)
deriving via (FromProfunctor (Joker f)) instance Functor f => LeftModule (->) Either Either (Joker f)
deriving via (FromProfunctor (WrappedArrow p)) instance ArrowChoice p => LeftModule (->) Either Either (WrappedArrow p)
deriving via (FromProfunctor (Sum p q)) instance (Choice p, Choice q) => LeftModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q)) instance (Choice p, Choice q) => LeftModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p)) instance (Functor f, Choice p) => LeftModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Procompose p q)) instance (Choice p, Choice q) => LeftModule (->) Either Either (Procompose p q)
deriving via (FromProfunctor (Cayley f q)) instance (Functor f, Choice q) => LeftModule (->) Either Either (Cayley f q)

instance LeftModule (->) Op Op (,) where
  lstrength :: (a, b) -> (Op a c, Op b c)
  lstrength = gbimap (Op . const) (Op . const)
  
instance LeftModule (->) Op Op Either where
  lstrength :: Either a b -> Either (Op a c) (Op b c)
  lstrength = gbimap (Op . const) (Op . const)

instance Bifunctor p => LeftModule (->) Op Op p where
  lstrength :: p a b -> p (Op a c) (Op b c)
  lstrength = bimap (Op . const) (Op . const)

--instance Closed p => LeftModule (->) Op Op p where  
--  lstrength :: p a b -> p (Op a c) (Op b c)
--  lstrength = dimap getOp Op . closed

--------------------------------------------------------------------------------
-- RightModule

-- | TODO
--
-- >>> :t rstrength @(->) @Either @Either @(->)
-- rstrength @(->) @Either @Either @(->) :: (a -> b) -> Either x a -> Either x b
--
-- >>> :t rstrength @(->) @(,) @(,) @(->)
-- rstrength @(->) @(,) @(,) @(->) :: (a -> b) -> (x, a) -> (x, b)
--
-- >>> :t rstrength @(->) @(,) @(,) @(Kleisli P.IO)
-- rstrength @(->) @(,) @(,) @(Kleisli P.IO) :: Kleisli IO a b -> Kleisli IO (x, a) (x, b)
class RightModule cat t1 t2 f where
  rstrength :: cat (f a b) (f (t1 x a) (t2 x b))

instance Strong p => RightModule (->) (,) (,) (FromProfunctor p) where
  rstrength :: FromProfunctor p a b -> FromProfunctor p (c, a) (c, b)
  rstrength (FromProfunctor pab) = FromProfunctor (second' pab)

instance Choice p => RightModule (->) Either Either (FromProfunctor p) where
  rstrength :: FromProfunctor p a b -> FromProfunctor p (Either c a) (Either c b)
  rstrength (FromProfunctor pab) = FromProfunctor (right' pab)

deriving via (FromProfunctor (Kleisli m)) instance Monad m => RightModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor (Pastro p)) instance RightModule (->) (,) (,) (Pastro p)
deriving via (FromProfunctor (Tambara p)) instance Profunctor p => RightModule (->) (,) (,) (Tambara p)
deriving via (FromProfunctor (Closure p)) instance Strong p => RightModule (->) (,) (,) (Closure p)
deriving via (FromProfunctor (FreeTraversing p)) instance RightModule (->) (,) (,) (FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => RightModule (->) (,) (,) (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p)) instance RightModule (->) (,) (,) (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p)) instance Profunctor p => RightModule (->) (,) (,) (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p)) instance Strong p => RightModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Yoneda p)) instance Strong p => RightModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->)) instance RightModule (->) (,) (,) (->)
deriving via (FromProfunctor (Forget r)) instance RightModule (->) (,) (,) (Forget r)
deriving via (FromProfunctor (Star m)) instance Functor m => RightModule (->) (,) (,) (Star m)
deriving via (FromProfunctor (Clown f)) instance Contravariant f => RightModule (->) (,) (,) (Clown f)
deriving via (FromProfunctor (WrappedArrow p)) instance Arrow p => RightModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q)) instance (Strong p, Strong q) => RightModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q)) instance (Strong p, Strong q) => RightModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Procompose p q)) instance (Strong p, Strong q) => RightModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f q)) instance (Functor f, Strong q) => RightModule (->) (,) (,) (Cayley f q)

deriving via (FromProfunctor (Kleisli m)) instance Monad m => RightModule (->) Either Either (Kleisli m)
deriving via (FromProfunctor Tagged) instance RightModule (->) Either Either Tagged
deriving via (FromProfunctor (Tambara p)) instance (Choice p) => RightModule (->) Either Either (Tambara p)
deriving via (FromProfunctor (PastroSum p)) instance RightModule (->) Either Either (PastroSum p)
deriving via (FromProfunctor (TambaraSum p)) instance Profunctor p => RightModule (->) Either Either (TambaraSum p)
deriving via (FromProfunctor (FreeTraversing p)) instance RightModule (->) Either Either ( FreeTraversing p) 
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => RightModule (->) Either Either (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p )) instance RightModule (->) Either Either (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p)) instance Profunctor p => RightModule (->) Either Either (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p)) instance Choice p => RightModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p)) instance Choice p => RightModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->)) instance RightModule (->) Either Either (->)
deriving via (FromProfunctor (Cokleisli w)) instance Comonad w => RightModule (->) Either Either (Cokleisli w)
deriving via (FromProfunctor (Forget r)) instance Monoid r => RightModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Star f)) instance Applicative f => RightModule (->) Either Either (Star f)
deriving via (FromProfunctor (Joker f)) instance Functor f => RightModule (->) Either Either (Joker f)
deriving via (FromProfunctor (WrappedArrow p)) instance ArrowChoice p => RightModule (->) Either Either (WrappedArrow p)
deriving via (FromProfunctor (Sum p q)) instance (Choice p, Choice q) => RightModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q)) instance (Choice p, Choice q) => RightModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p)) instance (Functor f, Choice p) => RightModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Procompose p q)) instance (Choice p, Choice q) => RightModule (->) Either Either (Procompose p q)
deriving via (FromProfunctor (Cayley f q)) instance (Functor f, Choice q) => RightModule (->) Either Either (Cayley f q)

instance RightModule (->) (->) (->) (,) where
  rstrength :: (a, b) -> (c -> a, c -> b)
  rstrength = bimap const const

instance RightModule (->) (->) (->) Either where
  rstrength :: Either a b -> Either (c -> a) (c -> b)
  rstrength = bimap const const

instance RightModule (->) (->) (->) These where
  rstrength :: These a b -> These (c -> a) (c -> b)
  rstrength = bimap const const

instance Bifunctor p => RightModule (->) (->) (->) p where
  rstrength :: p a b -> p (c -> a) (c -> b)
  rstrength = bimap const const

--instance Closed p => RightModule (->) (->) (->) p where
--  rstrength :: p a b -> p (c -> a) (c -> b)
--  rstrength = closed
 
--------------------------------------------------------------------------------
-- Bimodule

class (LeftModule cat t1 t2 f, RightModule cat t1 t2 f) => Bimodule cat t1 t2 f

instance Strong p => Bimodule (->) (,) (,) (FromProfunctor p) 
instance Choice p => Bimodule (->) Either Either (FromProfunctor p) 

--------------------------------------------------------------------------------
-- LeftCoModule

class LeftCoModule cat t1 t2 f where
  lcostrength :: cat (f (t1 a c) (t2 b c)) (f a b) 

instance Costrong p => LeftCoModule (->) (,) (,) p where
  lcostrength :: p (a, c) (b, c) -> p a b
  lcostrength = unfirst

instance Cochoice p => LeftCoModule (->) Either Either p where
  lcostrength :: p (Either a c) (Either b c) -> p a b
  lcostrength  = unleft

--------------------------------------------------------------------------------
-- RightCoModule

class RightCoModule cat t1 t2 f where
  rcostrength :: cat (f (c `t1` a) (c `t2` b)) (f a b) 

instance Costrong p => RightCoModule (->) (,) (,) p where
  rcostrength :: p (c, a) (c, b) -> p a b
  rcostrength = unsecond

instance Cochoice p => RightCoModule (->) Either Either p where
  rcostrength = unright

--------------------------------------------------------------------------------
-- CoBimodule

class (LeftCoModule cat t1 t2 f, RightCoModule cat t1 t2 f) => CoBimodule cat t1 t2 f

instance Costrong p => CoBimodule (->) (,) (,) p 
instance Cochoice p => CoBimodule (->) Either Either p 
