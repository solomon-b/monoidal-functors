module Data.Bifunctor.BiInvariant where

import Control.Arrow
import Control.Category.Tensor
import Control.Comonad
import Data.Bifunctor
import Data.Bifunctor.Biap
import Data.Bifunctor.Biff
import Data.Bifunctor.Clown
import Data.Bifunctor.Flip
import Data.Bifunctor.Joker
import Data.Bifunctor.Product
import Data.Bifunctor.Sum
import Data.Bifunctor.Tannen
import Data.Bifunctor.Wrapped
import Data.Coerce
import Data.Functor.Const
import Data.Functor.Contravariant
import Data.Kind
import Data.Profunctor
import Data.Profunctor.Cayley
import Data.Profunctor.Choice
import Data.Profunctor.Closed
import Data.Profunctor.Composition
import Data.Profunctor.Mapping
import Data.Profunctor.Ran
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Profunctor.Yoneda
import Data.Semigroup (Arg)
import Data.Tagged
import Data.These
import GHC.Generics (K1)
import Prelude


class BiInvariant p where
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> p a b -> p a' b'

-- BiInvariant witnesses an Isomorphism
biinvIso :: BiInvariant p => Iso (->) a a' -> Iso (->) b b' -> Iso (->) (p a b) (p a' b')
biinvIso (Iso f f') (Iso g g') = Iso (biinvmap f' f g' g) (biinvmap f f' g g')

newtype FromProfunctor p a b = FromProfunctor { runPro :: p a b}

instance Profunctor p => BiInvariant (FromProfunctor p) where
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> FromProfunctor p a b -> FromProfunctor p a' b'
  biinvmap f _ _ g = FromProfunctor . dimap f g . runPro

newtype FromBifunctor p a b = FromBifunctor { runBi :: p a b }

instance Bifunctor p => BiInvariant (FromBifunctor p) where
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> FromBifunctor p a b -> FromBifunctor p a' b'
  biinvmap _ f _ g = FromBifunctor . bimap f g . runBi

newtype FromContra f a = FromContra { runContra :: f a }

instance Contravariant f => Contravariant (FromContra f) where
  contramap f = FromContra . contramap f . runContra

newtype FromFunctor f a = FromFunctor { runFunctor :: f a }
  deriving Functor

type Coercible1 f = ((forall a b. Coercible a b => Coercible (f a) (f b)) :: Constraint)
type Coercible2 f = (forall a b c d. (Coercible a b, Coercible c d) => Coercible (f a c) (f b d) :: Constraint)

deriving via (FromProfunctor (->))                    instance BiInvariant (->)
deriving via (FromProfunctor (Biff p f g))           instance (Profunctor p, Functor f, Functor g) => BiInvariant (Biff (FromProfunctor p) f g)
deriving via (FromProfunctor (Cayley f q))           instance (Functor f, Profunctor q) => BiInvariant (Cayley f q)
deriving via (FromProfunctor (Closure p))            instance Profunctor p => BiInvariant (Closure p)
deriving via (FromProfunctor (Clown f :: * -> * -> *))  instance Contravariant f => BiInvariant (Clown (FromContra f) :: * -> * -> *)
deriving via (FromProfunctor (Codensity p))          instance Profunctor p => BiInvariant (Codensity p)
deriving via (FromProfunctor (CofreeMapping p))      instance Profunctor p => BiInvariant (CofreeMapping p)
deriving via (FromProfunctor (CofreeTraversing p))   instance Profunctor p => BiInvariant (CofreeTraversing p)
deriving via (FromProfunctor (Cokleisli w))          instance Functor w => BiInvariant (Cokleisli w)
deriving via (FromProfunctor (Copastro p))           instance BiInvariant (Copastro p)
deriving via (FromProfunctor (CopastroSum p))        instance BiInvariant (CopastroSum p)
deriving via (FromProfunctor (Costar f))             instance Functor f => BiInvariant (Costar f)
deriving via (FromProfunctor (Cotambara p))          instance BiInvariant (Cotambara p)
deriving via (FromProfunctor (CotambaraSum p))       instance BiInvariant (CotambaraSum p)
deriving via (FromProfunctor (Coyoneda p))           instance BiInvariant (Coyoneda p)
deriving via (FromProfunctor (Environment p))        instance BiInvariant (Environment p)
deriving via (FromProfunctor (Forget r :: * -> * -> *)) instance BiInvariant (Forget r :: * -> * -> *)
deriving via (FromProfunctor (FreeMapping p))        instance BiInvariant (FreeMapping p)
deriving via (FromProfunctor (FreeTraversing p))     instance BiInvariant (FreeTraversing p)
deriving via (FromProfunctor (Joker f :: * -> * -> *))  instance Functor f => BiInvariant (Joker (FromContra f) :: * -> * -> *)
deriving via (FromProfunctor (Kleisli m))            instance Monad m => BiInvariant (Kleisli m)
deriving via (FromProfunctor (Pastro p))             instance BiInvariant (Pastro p)
deriving via (FromProfunctor (PastroSum p))          instance BiInvariant (PastroSum p)
deriving via (FromProfunctor (Procompose p q))       instance (Profunctor p, Profunctor q) => BiInvariant (Procompose p q)
deriving via (FromProfunctor (Product p q))          instance (Profunctor p, Profunctor q) => BiInvariant (Product (FromProfunctor p) (FromProfunctor q))
deriving via (FromProfunctor (Ran p q))              instance (Profunctor p, Profunctor q) => BiInvariant (Ran p q)
deriving via (FromProfunctor (Rift p q))             instance (Profunctor p, Profunctor q) => BiInvariant (Rift p q)
deriving via (FromProfunctor (Star f))               instance Functor f => BiInvariant (Star (FromFunctor f))
deriving via (FromProfunctor (Sum p q))              instance (Profunctor p, Profunctor q) => BiInvariant (Sum (FromProfunctor p) (FromProfunctor q))
deriving via (FromProfunctor (Tagged :: * -> * -> *))   instance BiInvariant (Tagged :: * -> * -> *)
deriving via (FromProfunctor (Tambara p))            instance Profunctor p => BiInvariant (Tambara p)
deriving via (FromProfunctor (TambaraSum p))         instance Profunctor p => BiInvariant (TambaraSum p)
deriving via (FromProfunctor (Tannen f q))           instance (Functor f, Profunctor q) => BiInvariant (Tannen f q)
deriving via (FromProfunctor (WrappedArrow p))       instance Arrow p => BiInvariant (WrappedArrow p)
deriving via (FromProfunctor (Yoneda p))             instance BiInvariant (Yoneda p)

deriving via (FromBifunctor ((,,) x1))                 instance BiInvariant ((,,) x1)
deriving via (FromBifunctor ((,,,) x1 x2))             instance BiInvariant ((,,,) x1 x2)
deriving via (FromBifunctor ((,,,,) x1 x2 x3))         instance BiInvariant ((,,,,) x1 x2 x3)
deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4))     instance BiInvariant ((,,,,,) x1 x2 x3 x4)
deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance BiInvariant ((,,,,,,) x1 x2 x3 x4 x5)
deriving via (FromBifunctor (,))                       instance BiInvariant (,)
deriving via (FromBifunctor (Arg))                     instance BiInvariant (Arg)
deriving via (FromBifunctor (Biap bi))                 instance Bifunctor bi => BiInvariant (Biap bi)
deriving via (FromBifunctor (Biff p f g))              instance (Bifunctor p, Functor f, Functor g) => BiInvariant (Biff (FromBifunctor p) f g)
deriving via (FromBifunctor (Clown f :: * -> * -> *))     instance Functor f => BiInvariant (Clown (FromFunctor f) :: * -> * -> *)
deriving via (FromBifunctor (Const :: * -> * -> *))       instance BiInvariant (Const :: * -> * -> *)
deriving via (FromBifunctor (Either))                  instance BiInvariant (Either)
deriving via (FromBifunctor (Flip p))                  instance Bifunctor p => BiInvariant (Flip p)
deriving via (FromBifunctor (Joker f :: * -> * -> *))     instance Functor f => BiInvariant (Joker (FromFunctor f) :: * -> * -> *)
deriving via (FromBifunctor (K1 i :: * -> * -> *))        instance BiInvariant (K1 i :: * -> * -> *)
deriving via (FromBifunctor (Product p q))             instance (Bifunctor p, Bifunctor q) => BiInvariant (Product (FromBifunctor p) (FromBifunctor q))
deriving via (FromBifunctor (Sum p q))                 instance (Bifunctor p, Bifunctor q) => BiInvariant (Sum (FromBifunctor p) (FromBifunctor q))
deriving via (FromBifunctor (Tannen f q))              instance (Functor f, Coercible1 f, Bifunctor q) => BiInvariant (Tannen (FromFunctor f) (FromBifunctor q))
deriving via (FromBifunctor (These))                   instance BiInvariant (These)
deriving via (FromBifunctor (WrappedBifunctor p))      instance Bifunctor p => BiInvariant (WrappedBifunctor p)
