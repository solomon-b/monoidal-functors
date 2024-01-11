module Data.Bifunctor.BiInvariant
  ( -- * BiInvariant
    BiInvariant (..),
    biinvIso,
    type Coercible1,
    type Coercible2,
  )
where

--------------------------------------------------------------------------------

import Control.Arrow (Arrow, Kleisli (Kleisli))
import Control.Category.Tensor (Iso (Iso))
import Control.Comonad (Cokleisli (Cokleisli))
import Data.Bifunctor (Bifunctor (bimap))
import Data.Bifunctor.Biap (Biap (Biap))
import Data.Bifunctor.Biff (Biff (Biff))
import Data.Bifunctor.Clown (Clown (Clown))
import Data.Bifunctor.Flip (Flip (Flip))
import Data.Bifunctor.Joker (Joker (Joker))
import Data.Bifunctor.Product (Product)
import Data.Bifunctor.Sum (Sum)
import Data.Bifunctor.Tannen (Tannen (Tannen))
import Data.Bifunctor.Wrapped (WrappedBifunctor (WrapBifunctor))
import Data.Coerce (Coercible)
import Data.Functor.Const (Const (Const))
import Data.Functor.Contravariant (Contravariant (contramap))
import Data.Kind (Constraint)
import Data.Profunctor (Costar (Costar), Forget (Forget), Profunctor (dimap), Star (Star), WrappedArrow (WrapArrow))
import Data.Profunctor.Cayley (Cayley (Cayley))
import Data.Profunctor.Choice (CopastroSum (CopastroSum), CotambaraSum, PastroSum, TambaraSum (TambaraSum))
import Data.Profunctor.Closed (Closure (Closure), Environment)
import Data.Profunctor.Composition (Procompose, Rift (Rift))
import Data.Profunctor.Mapping (CofreeMapping (CofreeMapping), FreeMapping)
import Data.Profunctor.Ran (Codensity (Codensity), Ran (Ran))
import Data.Profunctor.Strong (Copastro (Copastro), Cotambara, Pastro, Tambara (Tambara))
import Data.Profunctor.Traversing (CofreeTraversing (CofreeTraversing), FreeTraversing)
import Data.Profunctor.Yoneda (Coyoneda, Yoneda (Yoneda))
import Data.Semigroup (Arg)
import Data.Tagged (Tagged (Tagged))
import Data.These (These)
import GHC.Generics (K1)
import Prelude

--------------------------------------------------------------------------------

-- | A bifunctor is 'BiInvariant' if it is parametric in both its type
-- parameters.
--
-- === Laws
--
-- @
-- 'biinvmap' 'id' 'id' 'id' 'id' ≡ 'id'
-- 'biinvmap' @g2@ @g2'@ @f2@ @f2'@ 'Control.Category..' 'Data.Functor.Invariant.invmap' @g1@ @g1'@ @f1@ @f1'@ ≡ 'Data.Functor.Invariant.invmap' (@g2@ 'Control.Category..' @g1@) (@g1'@ 'Control.Category..' @g2'@) (@f2@ 'Control.Category..' @f1@) (@f1'@ 'Control.Category..' @f2'@)
-- @
class BiInvariant p where
  -- | Used to apply a pair of isomorphic functions to @p a b@.
  -- 'Biinvmap' picks out the appropriate half of the iso depending if
  -- @p@ is covariant or contravariant on each parameter.
  --
  -- ==== __Examples__
  --
  -- >>> :t biinvmap @(,) (read @Int) show (read @Bool) show
  -- biinvmap @(,) (read @Int) show (read @Bool) show :: (Int, Bool) -> (String, String)
  --
  -- >>> biinvmap @(,) (read @Int) show (read @Bool) show (10, True)
  -- ("10","True")
  --
  -- >>> :t biinvmap @(->) (read @Int) show (read @Bool) show
  -- biinvmap @(->) (read @Int) show (read @Bool) show :: (Int -> Bool) -> String -> String
  --
  -- >>> biinvmap @(->) (read @Int) show (read @Bool) show (\i -> i > 10) "12"
  -- "True"
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> p a b -> p a' b'

-- | BiInvariant witnesses an Isomorphism
biinvIso :: (BiInvariant p) => Iso (->) a a' -> Iso (->) b b' -> Iso (->) (p a b) (p a' b')
biinvIso (Iso f f') (Iso g g') = Iso (biinvmap f' f g' g) (biinvmap f f' g g')

-- | Boilerplate newtype to derive 'BiInvariant' for any 'Profunctor'.
newtype FromProfunctor p a b = FromProfunctor {runPro :: p a b}

instance (Profunctor p) => BiInvariant (FromProfunctor p) where
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> FromProfunctor p a b -> FromProfunctor p a' b'
  biinvmap f _ _ g = FromProfunctor . dimap f g . runPro

-- | Boilerplate newtype to derive 'BiInvariant' for any 'Bifunctor'.
newtype FromBifunctor p a b = FromBifunctor {runBi :: p a b}

instance (Bifunctor p) => BiInvariant (FromBifunctor p) where
  biinvmap :: (a' -> a) -> (a -> a') -> (b' -> b) -> (b -> b') -> FromBifunctor p a b -> FromBifunctor p a' b'
  biinvmap _ f _ g = FromBifunctor . bimap f g . runBi

-- | Boilerplate newtype to derive 'BiInvariant' for any 'Contravariant'.
newtype FromContra f a = FromContra {runContra :: f a}

instance (Contravariant f) => Contravariant (FromContra f) where
  contramap :: (Contravariant f) => (a' -> a) -> FromContra f a -> FromContra f a'
  contramap f = FromContra . contramap f . runContra

newtype FromFunctor f a = FromFunctor (f a)
  deriving (Functor)

type Coercible1 f = ((forall a b. (Coercible a b) => Coercible (f a) (f b)) :: Constraint)

type Coercible2 f = (forall a b c d. (Coercible a b, Coercible c d) => Coercible (f a c) (f b d) :: Constraint)

deriving via (FromProfunctor (->)) instance BiInvariant (->)

deriving via (FromProfunctor (Biff p f g)) instance (Profunctor p, Functor f, Functor g) => BiInvariant (Biff (FromProfunctor p) f g)

deriving via (FromProfunctor (Cayley f q)) instance (Functor f, Profunctor q) => BiInvariant (Cayley f q)

deriving via (FromProfunctor (Closure p)) instance (Profunctor p) => BiInvariant (Closure p)

deriving via (FromProfunctor (Clown f :: * -> * -> *)) instance (Contravariant f) => BiInvariant (Clown (FromContra f) :: * -> * -> *)

deriving via (FromProfunctor (Codensity p)) instance (Profunctor p) => BiInvariant (Codensity p)

deriving via (FromProfunctor (CofreeMapping p)) instance (Profunctor p) => BiInvariant (CofreeMapping p)

deriving via (FromProfunctor (CofreeTraversing p)) instance (Profunctor p) => BiInvariant (CofreeTraversing p)

deriving via (FromProfunctor (Cokleisli w)) instance (Functor w) => BiInvariant (Cokleisli w)

deriving via (FromProfunctor (Copastro p)) instance BiInvariant (Copastro p)

deriving via (FromProfunctor (CopastroSum p)) instance BiInvariant (CopastroSum p)

deriving via (FromProfunctor (Costar f)) instance (Functor f) => BiInvariant (Costar f)

deriving via (FromProfunctor (Cotambara p)) instance BiInvariant (Cotambara p)

deriving via (FromProfunctor (CotambaraSum p)) instance BiInvariant (CotambaraSum p)

deriving via (FromProfunctor (Coyoneda p)) instance BiInvariant (Coyoneda p)

deriving via (FromProfunctor (Environment p)) instance BiInvariant (Environment p)

deriving via (FromProfunctor (Forget r :: * -> * -> *)) instance BiInvariant (Forget r :: * -> * -> *)

deriving via (FromProfunctor (FreeMapping p)) instance BiInvariant (FreeMapping p)

deriving via (FromProfunctor (FreeTraversing p)) instance BiInvariant (FreeTraversing p)

deriving via (FromProfunctor (Joker f :: * -> * -> *)) instance (Functor f) => BiInvariant (Joker (FromContra f) :: * -> * -> *)

deriving via (FromProfunctor (Kleisli m)) instance (Monad m) => BiInvariant (Kleisli m)

deriving via (FromProfunctor (Pastro p)) instance BiInvariant (Pastro p)

deriving via (FromProfunctor (PastroSum p)) instance BiInvariant (PastroSum p)

deriving via (FromProfunctor (Procompose p q)) instance (Profunctor p, Profunctor q) => BiInvariant (Procompose p q)

deriving via (FromProfunctor (Product p q)) instance (Profunctor p, Profunctor q) => BiInvariant (Product (FromProfunctor p) (FromProfunctor q))

deriving via (FromProfunctor (Ran p q)) instance (Profunctor p, Profunctor q) => BiInvariant (Ran p q)

deriving via (FromProfunctor (Rift p q)) instance (Profunctor p, Profunctor q) => BiInvariant (Rift p q)

deriving via (FromProfunctor (Star f)) instance (Functor f) => BiInvariant (Star (FromFunctor f))

deriving via (FromProfunctor (Star f)) instance (Functor f) => BiInvariant (Star (FromContra f))

deriving via (FromProfunctor (Sum p q)) instance (Profunctor p, Profunctor q) => BiInvariant (Sum (FromProfunctor p) (FromProfunctor q))

deriving via (FromProfunctor (Tagged :: * -> * -> *)) instance BiInvariant (Tagged :: * -> * -> *)

deriving via (FromProfunctor (Tambara p)) instance (Profunctor p) => BiInvariant (Tambara p)

deriving via (FromProfunctor (TambaraSum p)) instance (Profunctor p) => BiInvariant (TambaraSum p)

deriving via (FromProfunctor (Tannen f q)) instance (Functor f, Profunctor q) => BiInvariant (Tannen f q)

deriving via (FromProfunctor (WrappedArrow p)) instance (Arrow p) => BiInvariant (WrappedArrow p)

deriving via (FromProfunctor (Yoneda p)) instance BiInvariant (Yoneda p)

deriving via (FromBifunctor ((,,) x1)) instance BiInvariant ((,,) x1)

deriving via (FromBifunctor ((,,,) x1 x2)) instance BiInvariant ((,,,) x1 x2)

deriving via (FromBifunctor ((,,,,) x1 x2 x3)) instance BiInvariant ((,,,,) x1 x2 x3)

deriving via (FromBifunctor ((,,,,,) x1 x2 x3 x4)) instance BiInvariant ((,,,,,) x1 x2 x3 x4)

deriving via (FromBifunctor ((,,,,,,) x1 x2 x3 x4 x5)) instance BiInvariant ((,,,,,,) x1 x2 x3 x4 x5)

deriving via (FromBifunctor (,)) instance BiInvariant (,)

deriving via (FromBifunctor Arg) instance BiInvariant Arg

deriving via (FromBifunctor (Biap bi)) instance (Bifunctor bi) => BiInvariant (Biap bi)

deriving via (FromBifunctor (Biff p f g)) instance (Bifunctor p, Functor f, Functor g) => BiInvariant (Biff (FromBifunctor p) f g)

deriving via (FromBifunctor (Clown f :: * -> * -> *)) instance (Functor f) => BiInvariant (Clown (FromFunctor f) :: * -> * -> *)

deriving via (FromBifunctor (Const :: * -> * -> *)) instance BiInvariant (Const :: * -> * -> *)

deriving via (FromBifunctor Either) instance BiInvariant Either

deriving via (FromBifunctor (Flip p)) instance (Bifunctor p) => BiInvariant (Flip p)

deriving via (FromBifunctor (Joker f :: * -> * -> *)) instance (Functor f) => BiInvariant (Joker (FromFunctor f) :: * -> * -> *)

deriving via (FromBifunctor (K1 i :: * -> * -> *)) instance BiInvariant (K1 i :: * -> * -> *)

deriving via (FromBifunctor (Product p q)) instance (Bifunctor p, Bifunctor q) => BiInvariant (Product (FromBifunctor p) (FromBifunctor q))

deriving via (FromBifunctor (Sum p q)) instance (Bifunctor p, Bifunctor q) => BiInvariant (Sum (FromBifunctor p) (FromBifunctor q))

deriving via (FromBifunctor (Tannen f q)) instance (Functor f, Coercible1 f, Bifunctor q) => BiInvariant (Tannen (FromFunctor f) (FromBifunctor q))

deriving via (FromBifunctor These) instance BiInvariant These

deriving via (FromBifunctor (WrappedBifunctor p)) instance (Bifunctor p) => BiInvariant (WrappedBifunctor p)
