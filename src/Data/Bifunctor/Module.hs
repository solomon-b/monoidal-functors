module Data.Bifunctor.Module where

--------------------------------------------------------------------------------

import Control.Applicative (Applicative)
import Control.Arrow (Arrow, ArrowChoice, ArrowLoop, Kleisli (..))
import Control.Category.Tensor (GBifunctor (..))
import Control.Comonad (Cokleisli, Comonad)
import Control.Monad (Functor, Monad)
import Control.Monad.Fix (MonadFix)
import Data.Bifunctor (Bifunctor)
import Data.Bifunctor.Clown (Clown)
import Data.Bifunctor.Joker (Joker)
import Data.Bifunctor.Product (Product)
import Data.Bifunctor.Sum (Sum)
import Data.Bifunctor.Tannen (Tannen)
import Data.Either (Either (..))
import Data.Functor.Const (Const (..))
import Data.Functor.Contravariant (Contravariant, Op (..))
import Data.Kind (Type)
import Data.Monoid (Monoid)
import Data.Profunctor
import Data.Profunctor.Cayley (Cayley)
import Data.Profunctor.Choice (CopastroSum, CotambaraSum, PastroSum, TambaraSum)
import Data.Profunctor.Closed (Closure)
import Data.Profunctor.Composition (Procompose)
import Data.Profunctor.Mapping (CofreeMapping, FreeMapping)
import Data.Profunctor.Rep (Corepresentable)
import Data.Profunctor.Strong (Copastro, Pastro, Tambara)
import Data.Profunctor.Traversing (CofreeTraversing, FreeTraversing)
import Data.Profunctor.Yoneda (Coyoneda, Yoneda)
import Data.Semigroup (Arg)
import Data.Tagged (Tagged)
import Data.These (These (This, That))
import Data.Traversable (Traversable)
import Data.Tuple (fst, snd)
import GHC.Generics (K1 (..))

-----------------------------------------------------------------------

-- | Boilerplate newtype to derive modules for any 'Profunctor'.
newtype FromProfunctor p a b = FromProfunctor { runPro :: p a b}
  deriving newtype (Functor, Profunctor, Strong, Choice, Costrong, Cochoice)

-- | Boilerplate newtype to derive modules for any 'Bifunctor'.
newtype FromBifunctor p a b = FromBifunctor { runBi :: p a b }
  deriving newtype (Functor, Bifunctor)

-----------------------------------------------------------------------

class LeftModule cat t1 t2 f where
  lstrength :: cat (f a b) (f (t1 a c) (t2 b c))

instance Strong p => LeftModule (->) (,) (,) (FromProfunctor p) where
  lstrength :: FromProfunctor p a b -> FromProfunctor p (a, c) (b, c)
  lstrength = first'

instance Choice p => LeftModule (->) Either Either (FromProfunctor p) where
  lstrength :: FromProfunctor p a b -> FromProfunctor p (Either a c) (Either b c)
  lstrength = left'

instance Bifunctor p => LeftModule (->) Either Either (FromBifunctor p) where
  lstrength :: FromBifunctor p a b -> FromBifunctor p (Either a c) (Either b c)
  lstrength = gbimap Left Left

instance Bifunctor p => LeftModule (->) These These (FromBifunctor p) where
  lstrength :: FromBifunctor p a b -> FromBifunctor p (These a c) (These b c)
  lstrength = gbimap This This

instance Bifunctor p => LeftModule Op (,) (,) (FromBifunctor p) where
  lstrength :: Op (FromBifunctor p a b) (FromBifunctor p (a, c) (b, c))
  lstrength = Op (gbimap fst fst)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => LeftModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor (Pastro p))           instance LeftModule (->) (,) (,) (Pastro p)
deriving via (FromProfunctor (Tambara p))          instance Profunctor p => LeftModule (->) (,) (,) (Tambara p)
deriving via (FromProfunctor (Closure p))          instance Strong p => LeftModule (->) (,) (,) (Closure p)
deriving via (FromProfunctor (FreeTraversing p))   instance LeftModule (->) (,) (,) (FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => LeftModule (->) (,) (,) (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p))      instance LeftModule (->) (,) (,) (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => LeftModule (->) (,) (,) (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Strong p => LeftModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Strong p => LeftModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))                 instance LeftModule (->) (,) (,) (->)
deriving via (FromProfunctor (Forget r))           instance LeftModule (->) (,) (,) (Forget r)
deriving via (FromProfunctor (Star m))             instance Functor m => LeftModule (->) (,) (,) (Star m)
deriving via (FromProfunctor (Clown f))            instance Contravariant f => LeftModule (->) (,) (,) (Clown f)
deriving via (FromProfunctor (WrappedArrow p))     instance Arrow p => LeftModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f q))         instance (Functor f, Strong q) => LeftModule (->) (,) (,) (Tannen f q)
deriving via (FromProfunctor (Procompose p q))     instance (Strong p, Strong q) => LeftModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Strong q) => LeftModule (->) (,) (,) (Cayley f q)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => LeftModule (->) Either Either (Kleisli m)
deriving via (FromProfunctor Tagged)               instance LeftModule (->) Either Either Tagged
deriving via (FromProfunctor (Tambara p))          instance (Choice p) => LeftModule (->) Either Either (Tambara p)
deriving via (FromProfunctor (PastroSum p))        instance LeftModule (->) Either Either (PastroSum p)
deriving via (FromProfunctor (TambaraSum p))       instance Profunctor p => LeftModule (->) Either Either (TambaraSum p)
deriving via (FromProfunctor (FreeTraversing p))   instance LeftModule (->) Either Either ( FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => LeftModule (->) Either Either (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p ))     instance LeftModule (->) Either Either (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => LeftModule (->) Either Either (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Choice p => LeftModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Choice p => LeftModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))                 instance LeftModule (->) Either Either (->)
deriving via (FromProfunctor (Cokleisli w))        instance Comonad w => LeftModule (->) Either Either (Cokleisli w)
deriving via (FromProfunctor (Forget r))           instance Monoid r => LeftModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Star f))             instance Applicative f => LeftModule (->) Either Either (Star f)
deriving via (FromProfunctor (Joker f))            instance Functor f => LeftModule (->) Either Either (Joker f)
deriving via (FromProfunctor (WrappedArrow p))     instance ArrowChoice p => LeftModule (->) Either Either (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Choice p, Choice q) => LeftModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Choice p, Choice q) => LeftModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))         instance (Functor f, Choice p) => LeftModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Procompose p q))     instance (Choice p, Choice q) => LeftModule (->) Either Either (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Choice q) => LeftModule (->) Either Either (Cayley f q)

deriving via (FromBifunctor Arg)                       instance LeftModule (->) Either Either Arg
deriving via (FromBifunctor Const)                     instance LeftModule (->) Either Either Const
deriving via (FromBifunctor Either)                    instance LeftModule (->) Either Either Either
deriving via (FromBifunctor These)                     instance LeftModule (->) Either Either These
deriving via (FromBifunctor (K1 i))                    instance LeftModule (->) Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftModule (->) Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftModule (->) Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftModule (->) Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftModule (->) Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftModule (->) Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftModule (->) Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance LeftModule (->) These These Arg
deriving via (FromBifunctor Const)                     instance LeftModule (->) These These Const
deriving via (FromBifunctor Either)                    instance LeftModule (->) These These Either
deriving via (FromBifunctor These)                     instance LeftModule (->) These These These
deriving via (FromBifunctor (K1 i))                    instance LeftModule (->) These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftModule (->) These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftModule (->) These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftModule (->) These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftModule (->) These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftModule (->) These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftModule (->) These These ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance LeftModule Op (,) (,) Arg
deriving via (FromBifunctor Const)                     instance LeftModule Op (,) (,) Const
deriving via (FromBifunctor Either)                    instance LeftModule Op (,) (,) Either
deriving via (FromBifunctor These)                     instance LeftModule Op (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance LeftModule Op (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftModule Op (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftModule Op (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftModule Op (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftModule Op (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftModule Op (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftModule Op (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

--------------------------------------------------------------------------------

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
  rstrength :: cat (f a b) (f (x `t1` a) (x `t2` b))

instance Strong p => RightModule (->) (,) (,) (FromProfunctor p) where
  rstrength :: FromProfunctor p a b -> FromProfunctor p (c, a) (c, b)
  rstrength = second'

instance Choice p => RightModule (->) Either Either (FromProfunctor p) where
  rstrength :: FromProfunctor p a b -> FromProfunctor p (Either c a) (Either c b)
  rstrength = right'

instance Bifunctor p => RightModule (->) Either Either (FromBifunctor p) where
  rstrength :: FromBifunctor p a b -> FromBifunctor p (Either x a) (Either x b)
  rstrength = gbimap Right Right

instance Bifunctor p => RightModule (->) These These (FromBifunctor p) where
  rstrength :: FromBifunctor p a b -> FromBifunctor p (These x a) (These x b)
  rstrength = gbimap That That

instance Bifunctor p => RightModule Op (,) (,) (FromBifunctor p) where
  rstrength :: Op (FromBifunctor p a b) (FromBifunctor p (x, a) (x, b))
  rstrength = Op (gbimap snd snd)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => RightModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor (Pastro p))           instance RightModule (->) (,) (,) (Pastro p)
deriving via (FromProfunctor (Tambara p))          instance Profunctor p => RightModule (->) (,) (,) (Tambara p)
deriving via (FromProfunctor (Closure p))          instance Strong p => RightModule (->) (,) (,) (Closure p)
deriving via (FromProfunctor (FreeTraversing p))   instance RightModule (->) (,) (,) (FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => RightModule (->) (,) (,) (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p))      instance RightModule (->) (,) (,) (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => RightModule (->) (,) (,) (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Strong p => RightModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Strong p => RightModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))                 instance RightModule (->) (,) (,) (->)
deriving via (FromProfunctor (Forget r))           instance RightModule (->) (,) (,) (Forget r)
deriving via (FromProfunctor (Star m))             instance Functor m => RightModule (->) (,) (,) (Star m)
deriving via (FromProfunctor (Clown f))            instance Contravariant f => RightModule (->) (,) (,) (Clown f)
deriving via (FromProfunctor (WrappedArrow p))     instance Arrow p => RightModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Strong p, Strong q) => RightModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Strong p, Strong q) => RightModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f q))         instance (Functor f, Strong q) => RightModule (->) (,) (,) (Tannen f q)
deriving via (FromProfunctor (Procompose p q))     instance (Strong p, Strong q) => RightModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Strong q) => RightModule (->) (,) (,) (Cayley f q)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => RightModule (->) Either Either (Kleisli m)
deriving via (FromProfunctor Tagged)               instance RightModule (->) Either Either Tagged
deriving via (FromProfunctor (Tambara p))          instance (Choice p) => RightModule (->) Either Either (Tambara p)
deriving via (FromProfunctor (PastroSum p))        instance RightModule (->) Either Either (PastroSum p)
deriving via (FromProfunctor (TambaraSum p))       instance Profunctor p => RightModule (->) Either Either (TambaraSum p)
deriving via (FromProfunctor (FreeTraversing p))   instance RightModule (->) Either Either ( FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => RightModule (->) Either Either (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p ))     instance RightModule (->) Either Either (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => RightModule (->) Either Either (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Choice p => RightModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Choice p => RightModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))                 instance RightModule (->) Either Either (->)
deriving via (FromProfunctor (Cokleisli w))        instance Comonad w => RightModule (->) Either Either (Cokleisli w)
deriving via (FromProfunctor (Forget r))           instance Monoid r => RightModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Star f))             instance Applicative f => RightModule (->) Either Either (Star f)
deriving via (FromProfunctor (Joker f))            instance Functor f => RightModule (->) Either Either (Joker f)
deriving via (FromProfunctor (WrappedArrow p))     instance ArrowChoice p => RightModule (->) Either Either (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Choice p, Choice q) => RightModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Choice p, Choice q) => RightModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))         instance (Functor f, Choice p) => RightModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Procompose p q))     instance (Choice p, Choice q) => RightModule (->) Either Either (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Choice q) => RightModule (->) Either Either (Cayley f q)

deriving via (FromBifunctor Arg)                       instance RightModule (->) Either Either Arg
deriving via (FromBifunctor Const)                     instance RightModule (->) Either Either Const
deriving via (FromBifunctor Either)                    instance RightModule (->) Either Either Either
deriving via (FromBifunctor These)                     instance RightModule (->) Either Either These
deriving via (FromBifunctor (K1 i))                    instance RightModule (->) Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightModule (->) Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightModule (->) Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightModule (->) Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightModule (->) Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightModule (->) Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightModule (->) Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance RightModule (->) These These Arg
deriving via (FromBifunctor Const)                     instance RightModule (->) These These Const
deriving via (FromBifunctor Either)                    instance RightModule (->) These These Either
deriving via (FromBifunctor These)                     instance RightModule (->) These These These
deriving via (FromBifunctor (K1 i))                    instance RightModule (->) These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightModule (->) These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightModule (->) These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightModule (->) These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightModule (->) These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightModule (->) These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightModule (->) These These ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance RightModule Op (,) (,) Arg
deriving via (FromBifunctor Const)                     instance RightModule Op (,) (,) Const
deriving via (FromBifunctor Either)                    instance RightModule Op (,) (,) Either
deriving via (FromBifunctor These)                     instance RightModule Op (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance RightModule Op (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightModule Op (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightModule Op (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightModule Op (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightModule Op (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightModule Op (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightModule Op (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

--------------------------------------------------------------------------------

class (LeftModule cat t1 t2 f, RightModule cat t1 t2 f) => Bimodule cat t1 t2 f

instance Strong p => Bimodule (->) (,) (,) (FromProfunctor p)
instance Choice p => Bimodule (->) Either Either (FromProfunctor p)
instance Bifunctor p => Bimodule (->) Either Either (FromBifunctor p)
instance Bifunctor p => Bimodule (->) These These (FromBifunctor p)
instance Bifunctor p => Bimodule Op (,) (,) (FromBifunctor p)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => Bimodule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor (Pastro p))           instance Bimodule (->) (,) (,) (Pastro p)
deriving via (FromProfunctor (Tambara p))          instance Profunctor p => Bimodule (->) (,) (,) (Tambara p)
deriving via (FromProfunctor (Closure p))          instance Strong p => Bimodule (->) (,) (,) (Closure p)
deriving via (FromProfunctor (FreeTraversing p))   instance Bimodule (->) (,) (,) (FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => Bimodule (->) (,) (,) (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p))      instance Bimodule (->) (,) (,) (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => Bimodule (->) (,) (,) (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Strong p => Bimodule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Strong p => Bimodule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))                 instance Bimodule (->) (,) (,) (->)
deriving via (FromProfunctor (Forget r))           instance Bimodule (->) (,) (,) (Forget r)
deriving via (FromProfunctor (Star m))             instance Functor m => Bimodule (->) (,) (,) (Star m)
deriving via (FromProfunctor (Clown f))            instance Contravariant f => Bimodule (->) (,) (,) (Clown f)
deriving via (FromProfunctor (WrappedArrow p))     instance Arrow p => Bimodule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Strong p, Strong q) => Bimodule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Strong p, Strong q) => Bimodule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f q))         instance (Functor f, Strong q) => Bimodule (->) (,) (,) (Tannen f q)
deriving via (FromProfunctor (Procompose p q))     instance (Strong p, Strong q) => Bimodule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Strong q) => Bimodule (->) (,) (,) (Cayley f q)

deriving via (FromProfunctor (Kleisli m))          instance Monad m => Bimodule (->) Either Either (Kleisli m)
deriving via (FromProfunctor Tagged)               instance Bimodule (->) Either Either Tagged
deriving via (FromProfunctor (Tambara p))          instance (Choice p) => Bimodule (->) Either Either (Tambara p)
deriving via (FromProfunctor (PastroSum p))        instance Bimodule (->) Either Either (PastroSum p)
deriving via (FromProfunctor (TambaraSum p))       instance Profunctor p => Bimodule (->) Either Either (TambaraSum p)
deriving via (FromProfunctor (FreeTraversing p))   instance Bimodule (->) Either Either ( FreeTraversing p)
deriving via (FromProfunctor (CofreeTraversing p)) instance Profunctor p => Bimodule (->) Either Either (CofreeTraversing p)
deriving via (FromProfunctor (FreeMapping p ))     instance Bimodule (->) Either Either (FreeMapping p)
deriving via (FromProfunctor (CofreeMapping p))    instance Profunctor p => Bimodule (->) Either Either (CofreeMapping p)
deriving via (FromProfunctor (Coyoneda p))         instance Choice p => Bimodule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))           instance Choice p => Bimodule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))                 instance Bimodule (->) Either Either (->)
deriving via (FromProfunctor (Cokleisli w))        instance Comonad w => Bimodule (->) Either Either (Cokleisli w)
deriving via (FromProfunctor (Forget r))           instance Monoid r => Bimodule (->) Either Either (Forget r)
deriving via (FromProfunctor (Star f))             instance Applicative f => Bimodule (->) Either Either (Star f)
deriving via (FromProfunctor (Joker f))            instance Functor f => Bimodule (->) Either Either (Joker f)
deriving via (FromProfunctor (WrappedArrow p))     instance ArrowChoice p => Bimodule (->) Either Either (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))            instance (Choice p, Choice q) => Bimodule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))        instance (Choice p, Choice q) => Bimodule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))         instance (Functor f, Choice p) => Bimodule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Procompose p q))     instance (Choice p, Choice q) => Bimodule (->) Either Either (Procompose p q)
deriving via (FromProfunctor (Cayley f q))         instance (Functor f, Choice q) => Bimodule (->) Either Either (Cayley f q)

deriving via (FromBifunctor Arg)                       instance Bimodule (->) Either Either Arg
deriving via (FromBifunctor Const)                     instance Bimodule (->) Either Either Const
deriving via (FromBifunctor Either)                    instance Bimodule (->) Either Either Either
deriving via (FromBifunctor These)                     instance Bimodule (->) Either Either These
deriving via (FromBifunctor (K1 i))                    instance Bimodule (->) Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance Bimodule (->) Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance Bimodule (->) Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance Bimodule (->) Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance Bimodule (->) Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance Bimodule (->) Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance Bimodule (->) Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance Bimodule (->) These These Arg
deriving via (FromBifunctor Const)                     instance Bimodule (->) These These Const
deriving via (FromBifunctor Either)                    instance Bimodule (->) These These Either
deriving via (FromBifunctor These)                     instance Bimodule (->) These These These
deriving via (FromBifunctor (K1 i))                    instance Bimodule (->) These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance Bimodule (->) These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance Bimodule (->) These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance Bimodule (->) These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance Bimodule (->) These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance Bimodule (->) These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance Bimodule (->) These These ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance Bimodule Op (,) (,) Arg
deriving via (FromBifunctor Const)                     instance Bimodule Op (,) (,) Const
deriving via (FromBifunctor Either)                    instance Bimodule Op (,) (,) Either
deriving via (FromBifunctor These)                     instance Bimodule Op (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance Bimodule Op (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance Bimodule Op (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance Bimodule Op (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance Bimodule Op (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance Bimodule Op (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance Bimodule Op (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance Bimodule Op (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

--------------------------------------------------------------------------------

class LeftCoModule cat t1 t2 f where
  lcostrength :: cat (f (t1 a c) (t2 b c)) (f a b)

instance Costrong p => LeftCoModule (->) (,) (,) (FromProfunctor p) where
  lcostrength :: FromProfunctor p (a, c) (b, c) -> FromProfunctor p a b
  lcostrength = unfirst

instance Cochoice p => LeftCoModule (->) Either Either (FromProfunctor p) where
  lcostrength  = unleft

instance Bifunctor p => LeftCoModule (->) (,) (,) (FromBifunctor p) where
  lcostrength = gbimap fst fst

instance Bifunctor p => LeftCoModule Op Either Either (FromBifunctor p) where
  lcostrength = Op (gbimap Left Left)

instance Bifunctor p => LeftCoModule Op These These (FromBifunctor p) where
  lcostrength = Op (gbimap This This)

deriving via (FromProfunctor (Kleisli m))      instance MonadFix m => LeftCoModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor Tagged)           instance LeftCoModule (->) (,) (,) Tagged
deriving via (FromProfunctor (Coyoneda p))     instance Costrong p => LeftCoModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Copastro p))     instance Cochoice p => LeftCoModule (->) (,) (,) (Copastro p)
deriving via (FromProfunctor (Yoneda p))       instance Costrong p => LeftCoModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))             instance LeftCoModule (->) (,) (,) (->)
deriving via (FromProfunctor (Cokleisli f))    instance Functor f => LeftCoModule (->) (,) (,) (Cokleisli f)
deriving via (FromProfunctor (Costar f))       instance Functor f => LeftCoModule (->) (,) (,) (Costar f)
deriving via (FromProfunctor (WrappedArrow p)) instance ArrowLoop p => LeftCoModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))        instance (Costrong p, Costrong q) => LeftCoModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Costrong p, Costrong q) => LeftCoModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Costrong p) => LeftCoModule (->) (,) (,) (Tannen f p)
deriving via (FromProfunctor (Procompose p q)) instance (Corepresentable p, Corepresentable q) => LeftCoModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Costrong p) => LeftCoModule (->) (,) (,) (Cayley f p)

deriving via (FromProfunctor (CopastroSum p))  instance LeftCoModule (->) Either Either (CopastroSum p)
deriving via (FromProfunctor (CotambaraSum p)) instance LeftCoModule (->) Either Either (CotambaraSum p)
deriving via (FromProfunctor (Coyoneda p))     instance Cochoice p => LeftCoModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))       instance Cochoice p => LeftCoModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))             instance LeftCoModule (->) Either Either (->)
deriving via (FromProfunctor (Forget r))       instance LeftCoModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Costar f))       instance Applicative f => LeftCoModule (->) Either Either (Costar f)
deriving via (FromProfunctor (Star f))         instance Traversable f => LeftCoModule (->) Either Either (Star f)
deriving via (FromProfunctor (Sum p q))        instance (Cochoice p, Cochoice q) => LeftCoModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Cochoice p, Cochoice q) => LeftCoModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Cochoice p) => LeftCoModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Cochoice p) => LeftCoModule (->) Either Either (Cayley f p)

deriving via (FromBifunctor Arg)                       instance LeftCoModule (->) (,) (,) Arg
deriving via (FromBifunctor Const)                     instance LeftCoModule (->) (,) (,) Const
deriving via (FromBifunctor Either)                    instance LeftCoModule (->) (,) (,) Either
deriving via (FromBifunctor These)                     instance LeftCoModule (->) (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance LeftCoModule (->) (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftCoModule (->) (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftCoModule (->) (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftCoModule (->) (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftCoModule (->) (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftCoModule (->) (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftCoModule (->) (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance LeftCoModule Op Either Either Arg
deriving via (FromBifunctor Const)                     instance LeftCoModule Op Either Either Const
deriving via (FromBifunctor Either)                    instance LeftCoModule Op Either Either Either
deriving via (FromBifunctor These)                     instance LeftCoModule Op Either Either These
deriving via (FromBifunctor (K1 i))                    instance LeftCoModule Op Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftCoModule Op Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftCoModule Op Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftCoModule Op Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftCoModule Op Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftCoModule Op Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftCoModule Op Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance LeftCoModule Op These These Arg
deriving via (FromBifunctor Const)                     instance LeftCoModule Op These These Const
deriving via (FromBifunctor Either)                    instance LeftCoModule Op These These Either
deriving via (FromBifunctor These)                     instance LeftCoModule Op These These These
deriving via (FromBifunctor (K1 i))                    instance LeftCoModule Op These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance LeftCoModule Op These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance LeftCoModule Op These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance LeftCoModule Op These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance LeftCoModule Op These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance LeftCoModule Op These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance LeftCoModule Op These These ((,,,,,,) x1 x2 x3 x4 x5)

--------------------------------------------------------------------------------

class RightCoModule cat t1 t2 f where
  rcostrength :: cat (f (c `t1` a) (c `t2` b)) (f a b)

instance Costrong p => RightCoModule (->) (,) (,) (FromProfunctor p) where
  rcostrength :: FromProfunctor p (c, a) (c, b) -> FromProfunctor p a b
  rcostrength = unsecond

instance Cochoice p => RightCoModule (->) Either Either (FromProfunctor p) where
  rcostrength :: FromProfunctor p (Either c a) (Either c b) -> FromProfunctor p a b
  rcostrength = unright

instance Bifunctor p => RightCoModule (->) (,) (,) (FromBifunctor p) where
  rcostrength :: FromBifunctor p (c, a) (c, b) -> FromBifunctor p a b
  rcostrength = gbimap snd snd

instance Bifunctor p => RightCoModule Op Either Either (FromBifunctor p) where
  rcostrength :: Op (FromBifunctor p (Either c a) (Either c b)) (FromBifunctor p a b)
  rcostrength = Op (gbimap Right Right)

instance Bifunctor p => RightCoModule Op These These (FromBifunctor p) where
  rcostrength :: Op (FromBifunctor p (These c a) (These c b)) (FromBifunctor p a b)
  rcostrength = Op (gbimap That That)

deriving via (FromProfunctor (Kleisli m))      instance MonadFix m => RightCoModule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor Tagged)           instance RightCoModule (->) (,) (,) Tagged
deriving via (FromProfunctor (Coyoneda p))     instance Costrong p => RightCoModule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Copastro p))     instance Cochoice p => RightCoModule (->) (,) (,) (Copastro p)
deriving via (FromProfunctor (Yoneda p))       instance Costrong p => RightCoModule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))             instance RightCoModule (->) (,) (,) (->)
deriving via (FromProfunctor (Cokleisli f))    instance Functor f => RightCoModule (->) (,) (,) (Cokleisli f)
deriving via (FromProfunctor (Costar f))       instance Functor f => RightCoModule (->) (,) (,) (Costar f)
deriving via (FromProfunctor (WrappedArrow p)) instance ArrowLoop p => RightCoModule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))        instance (Costrong p, Costrong q) => RightCoModule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Costrong p, Costrong q) => RightCoModule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Costrong p) => RightCoModule (->) (,) (,) (Tannen f p)
deriving via (FromProfunctor (Procompose p q)) instance (Corepresentable p, Corepresentable q) => RightCoModule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Costrong p) => RightCoModule (->) (,) (,) (Cayley f p)

deriving via (FromProfunctor (CopastroSum p))  instance RightCoModule (->) Either Either (CopastroSum p)
deriving via (FromProfunctor (CotambaraSum p)) instance RightCoModule (->) Either Either (CotambaraSum p)
deriving via (FromProfunctor (Coyoneda p))     instance Cochoice p => RightCoModule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))       instance Cochoice p => RightCoModule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))             instance RightCoModule (->) Either Either (->)
deriving via (FromProfunctor (Forget r))       instance RightCoModule (->) Either Either (Forget r)
deriving via (FromProfunctor (Costar f))       instance Applicative f => RightCoModule (->) Either Either (Costar f)
deriving via (FromProfunctor (Star f))         instance Traversable f => RightCoModule (->) Either Either (Star f)
deriving via (FromProfunctor (Sum p q))        instance (Cochoice p, Cochoice q) => RightCoModule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Cochoice p, Cochoice q) => RightCoModule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Cochoice p) => RightCoModule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Cochoice p) => RightCoModule (->) Either Either (Cayley f p)

deriving via (FromBifunctor Arg)                       instance RightCoModule (->) (,) (,) Arg
deriving via (FromBifunctor Const)                     instance RightCoModule (->) (,) (,) Const
deriving via (FromBifunctor Either)                    instance RightCoModule (->) (,) (,) Either
deriving via (FromBifunctor These)                     instance RightCoModule (->) (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance RightCoModule (->) (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightCoModule (->) (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightCoModule (->) (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightCoModule (->) (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightCoModule (->) (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightCoModule (->) (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightCoModule (->) (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance RightCoModule Op Either Either Arg
deriving via (FromBifunctor Const)                     instance RightCoModule Op Either Either Const
deriving via (FromBifunctor Either)                    instance RightCoModule Op Either Either Either
deriving via (FromBifunctor These)                     instance RightCoModule Op Either Either These
deriving via (FromBifunctor (K1 i))                    instance RightCoModule Op Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightCoModule Op Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightCoModule Op Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightCoModule Op Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightCoModule Op Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightCoModule Op Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightCoModule Op Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance RightCoModule Op These These Arg
deriving via (FromBifunctor Const)                     instance RightCoModule Op These These Const
deriving via (FromBifunctor Either)                    instance RightCoModule Op These These Either
deriving via (FromBifunctor These)                     instance RightCoModule Op These These These
deriving via (FromBifunctor (K1 i))                    instance RightCoModule Op These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance RightCoModule Op These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance RightCoModule Op These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance RightCoModule Op These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance RightCoModule Op These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance RightCoModule Op These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance RightCoModule Op These These ((,,,,,,) x1 x2 x3 x4 x5)

--------------------------------------------------------------------------------

class (LeftCoModule cat t1 t2 f, RightCoModule cat t1 t2 f) => CoBimodule cat t1 t2 f

instance Costrong p => CoBimodule (->) (,) (,) (FromProfunctor p)
instance Cochoice p => CoBimodule (->) Either Either (FromProfunctor p)
instance Bifunctor p => CoBimodule (->) (,) (,) (FromBifunctor p)
instance Bifunctor p => CoBimodule Op Either Either (FromBifunctor p)
instance Bifunctor p => CoBimodule Op These These (FromBifunctor p)

deriving via (FromProfunctor (Kleisli m))      instance MonadFix m => CoBimodule (->) (,) (,) (Kleisli m)
deriving via (FromProfunctor Tagged)           instance CoBimodule (->) (,) (,) Tagged
deriving via (FromProfunctor (Coyoneda p))     instance Costrong p => CoBimodule (->) (,) (,) (Coyoneda p)
deriving via (FromProfunctor (Copastro p))     instance Cochoice p => CoBimodule (->) (,) (,) (Copastro p)
deriving via (FromProfunctor (Yoneda p))       instance Costrong p => CoBimodule (->) (,) (,) (Yoneda p)
deriving via (FromProfunctor (->))             instance CoBimodule (->) (,) (,) (->)
deriving via (FromProfunctor (Cokleisli f))    instance Functor f => CoBimodule (->) (,) (,) (Cokleisli f)
deriving via (FromProfunctor (Costar f))       instance Functor f => CoBimodule (->) (,) (,) (Costar f)
deriving via (FromProfunctor (WrappedArrow p)) instance ArrowLoop p => CoBimodule (->) (,) (,) (WrappedArrow p)
deriving via (FromProfunctor (Sum p q))        instance (Costrong p, Costrong q) => CoBimodule (->) (,) (,) (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Costrong p, Costrong q) => CoBimodule (->) (,) (,) (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Costrong p) => CoBimodule (->) (,) (,) (Tannen f p)
deriving via (FromProfunctor (Procompose p q)) instance (Corepresentable p, Corepresentable q) => CoBimodule (->) (,) (,) (Procompose p q)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Costrong p) => CoBimodule (->) (,) (,) (Cayley f p)

deriving via (FromProfunctor (CopastroSum p))  instance CoBimodule (->) Either Either (CopastroSum p)
deriving via (FromProfunctor (CotambaraSum p)) instance CoBimodule (->) Either Either (CotambaraSum p)
deriving via (FromProfunctor (Coyoneda p))     instance Cochoice p => CoBimodule (->) Either Either (Coyoneda p)
deriving via (FromProfunctor (Yoneda p))       instance Cochoice p => CoBimodule (->) Either Either (Yoneda p)
deriving via (FromProfunctor (->))             instance CoBimodule (->) Either Either (->)
deriving via (FromProfunctor (Forget r))       instance CoBimodule (->) Either Either (Forget r)
deriving via (FromProfunctor (Costar f))       instance Applicative f => CoBimodule (->) Either Either (Costar f)
deriving via (FromProfunctor (Star f))         instance Traversable f => CoBimodule (->) Either Either (Star f)
deriving via (FromProfunctor (Sum p q))        instance (Cochoice p, Cochoice q) => CoBimodule (->) Either Either (Sum p q)
deriving via (FromProfunctor (Product p q))    instance (Cochoice p, Cochoice q) => CoBimodule (->) Either Either (Product p q)
deriving via (FromProfunctor (Tannen f p))     instance (Functor f, Cochoice p) => CoBimodule (->) Either Either (Tannen f p)
deriving via (FromProfunctor (Cayley f p))     instance (Functor f, Cochoice p) => CoBimodule (->) Either Either (Cayley f p)

deriving via (FromBifunctor Arg)                       instance CoBimodule (->) (,) (,) Arg
deriving via (FromBifunctor Const)                     instance CoBimodule (->) (,) (,) Const
deriving via (FromBifunctor Either)                    instance CoBimodule (->) (,) (,) Either
deriving via (FromBifunctor These)                     instance CoBimodule (->) (,) (,) These
deriving via (FromBifunctor (K1 i))                    instance CoBimodule (->) (,) (,) (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance CoBimodule (->) (,) (,) (,)
deriving via (FromBifunctor ((,,) x1))                 instance CoBimodule (->) (,) (,) ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance CoBimodule (->) (,) (,) ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance CoBimodule (->) (,) (,) ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance CoBimodule (->) (,) (,) ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance CoBimodule (->) (,) (,) ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance CoBimodule Op Either Either Arg
deriving via (FromBifunctor Const)                     instance CoBimodule Op Either Either Const
deriving via (FromBifunctor Either)                    instance CoBimodule Op Either Either Either
deriving via (FromBifunctor These)                     instance CoBimodule Op Either Either These
deriving via (FromBifunctor (K1 i))                    instance CoBimodule Op Either Either (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance CoBimodule Op Either Either (,)
deriving via (FromBifunctor ((,,) x1))                 instance CoBimodule Op Either Either ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance CoBimodule Op Either Either ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance CoBimodule Op Either Either ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance CoBimodule Op Either Either ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance CoBimodule Op Either Either ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor Arg)                       instance CoBimodule Op These These Arg
deriving via (FromBifunctor Const)                     instance CoBimodule Op These These Const
deriving via (FromBifunctor Either)                    instance CoBimodule Op These These Either
deriving via (FromBifunctor These)                     instance CoBimodule Op These These These
deriving via (FromBifunctor (K1 i))                    instance CoBimodule Op These These (K1 i :: Type -> Type -> Type)
deriving via (FromBifunctor (,))                       instance CoBimodule Op These These (,)
deriving via (FromBifunctor ((,,) x1))                 instance CoBimodule Op These These ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance CoBimodule Op These These ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance CoBimodule Op These These ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance CoBimodule Op These These ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance CoBimodule Op These These ((,,,,,,) x1 x2 x3 x4 x5)
