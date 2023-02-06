module Data.Functor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,
  )
where

--------------------------------------------------------------------------------

import Control.Applicative
import Control.Arrow (ArrowMonad, ArrowPlus, ArrowZero, Kleisli)
import Control.Category.Tensor
import Control.Monad (MonadPlus)
import Data.Align
import Data.Functor.Compose (Compose)
import Data.Functor.Identity
import Data.Functor.Product (Product)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (Alt, Ap)
import Data.Proxy (Proxy)
import Data.Tagged (Tagged)
import Data.These
import Data.Void
import GHC.Conc (STM)
import GHC.Generics (M1, Rec1, U1, type (:*:), type (:.:))
import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)
import Prelude
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible (divided, Divisible)
import Control.Monad.Trans.Maybe
import Data.Functor.Reverse (Reverse)
import Data.Functor.Constant
import Control.Monad.Trans.Writer.Strict (WriterT)
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.State.Strict (StateT)
import qualified Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.Reader (ReaderT)
import Control.Comonad.Identity (IdentityT)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Error (ErrorT)
import Control.Applicative.Backwards (Backwards)
import Data.Functor.Contravariant.Compose (ComposeCF, ComposeFC)
import Control.Monad.Trans.RWS.Strict (RWST)
import qualified Control.Monad.Trans.RWS.Lazy as Lazy

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Semigroupal' if it supports a natural transformation
-- \(\phi_{A,B} : F\ A \bullet F\ B \to F\ (A \otimes B)\), which we call 'combine'.
--
-- === Laws
--
-- __Associativity:__
--
-- \[ 
-- \require{AMScd}
-- \begin{CD}
-- (F A \bullet F B) \bullet F C @>>{\alpha_{\mathcal{D}}}>     F A \bullet (F B \bullet F C) \\
-- @VV{\phi_{A,B} \bullet 1}V                                   @VV{1 \bullet \phi_{B,C}}V \\
-- F (A \otimes B) \bullet F C   @.                             F A \bullet (F (B \otimes C)) \\
-- @VV{\phi_{A \otimes B,C}}V                                   @VV{\phi_{A,B \otimes C}}V \\
-- F ((A \otimes B) \otimes C)   @>>{F \alpha_{\mathcal{C}}}>   F (A \otimes (B \otimes C)) \\
-- \end{CD}
-- \]
--
-- @
-- 'combine' 'Control.Category..' 'grmap' 'combine' 'Control.Category..' 'bwd' 'assoc' ≡ 'fmap' ('bwd' 'assoc') 'Control.Category..' 'combine' 'Control.Category..' 'glmap' 'combine'
-- @
class (Associative cat t1, Associative cat t0) => Semigroupal cat t1 t0 f where
  -- | @combine@ is a natural transformation from functors \(\mathcal{C} × \mathcal{C}\) to \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Just "hello")
  -- Just (True,"hello")
  --
  -- >>> combine @(->) @(,) @(,) @Maybe (Just True, Nothing)
  -- Nothing
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Just True, Nothing)
  -- Just (Left True)
  --
  -- >>> combine @(->) @Either @(,) @Maybe (Nothing, Just "hello")
  -- Just (Right "hello")
  combine :: (f x `t0` f x') `cat` f (x `t1` x')

newtype FromApplicative f a = FromApplicative (f a)
  deriving newtype (Functor, Applicative)

instance Applicative f => Semigroupal (->) (,) (,) (FromApplicative f) where
  combine :: (FromApplicative f x, FromApplicative f x') -> FromApplicative f (x, x')
  combine = uncurry (liftA2 (,))

deriving via FromApplicative Identity           instance Semigroupal (->) (,) (,) Identity
deriving via FromApplicative (Compose f g)      instance (Applicative f, Applicative g) => Semigroupal (->) (,) (,) (Compose f g)
deriving via FromApplicative []                 instance Semigroupal (->) (,) (,) []
deriving via FromApplicative ZipList            instance Semigroupal (->) (,) (,) ZipList
deriving via FromApplicative NonEmpty           instance Semigroupal (->) (,) (,) NonEmpty
deriving via FromApplicative Maybe              instance Semigroupal (->) (,) (,) Maybe
deriving via FromApplicative (Either e)         instance Semigroupal (->) (,) (,) (Either e)
deriving via FromApplicative IO                 instance Semigroupal (->) (,) (,) IO
deriving via FromApplicative (Product f g)      instance (Applicative f, Applicative g) => Semigroupal (->) (,) (,) (Product f g)
deriving via (FromApplicative ((,) x1))         instance (Monoid x1) => Semigroupal (->) (,) (,) ((,) x1)
deriving via (FromApplicative ((,,) x1 x2))     instance (Monoid x1, Monoid x2) => Semigroupal (->) (,) (,) ((,,) x1 x2)
deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Semigroupal (->) (,) (,) ((,,,) x1 x2 x3)

newtype FromAlternative f a = FromAlternative (f a)
  deriving newtype (Functor, Applicative, Alternative)

instance Alternative f => Semigroupal (->) Either (,) (FromAlternative f) where
  combine :: (FromAlternative f x, FromAlternative f x') -> FromAlternative f (Either x x')
  combine (fx, fx') = fmap Left fx <|> fmap Right fx'

deriving via FromAlternative ZipList                 instance Semigroupal (->) Either (,) ZipList
deriving via FromAlternative STM                     instance Semigroupal (->) Either (,) STM
deriving via FromAlternative ReadP                   instance Semigroupal (->) Either (,) ReadP
deriving via FromAlternative ReadPrec                instance Semigroupal (->) Either (,) ReadPrec
deriving via FromAlternative IO                      instance Semigroupal (->) Either (,) IO
deriving via FromAlternative Maybe                   instance Semigroupal (->) Either (,) Maybe
deriving via FromAlternative []                      instance Semigroupal (->) Either (,) []
deriving via FromAlternative (WrappedMonad m)        instance (MonadPlus m) => Semigroupal (->) Either (,) (WrappedMonad m)
deriving via FromAlternative (ArrowMonad a)          instance (ArrowPlus a) => Semigroupal (->) Either (,) (ArrowMonad a)
deriving via FromAlternative (Proxy :: Type -> Type) instance Semigroupal (->) Either (,) (Proxy :: Type -> Type)
deriving via FromAlternative (U1 :: Type -> Type)    instance Semigroupal (->) Either (,) (U1 :: Type -> Type)
deriving via FromAlternative (WrappedArrow a b)      instance (ArrowZero a, ArrowPlus a) => Semigroupal (->) Either (,) (WrappedArrow a b)
deriving via FromAlternative (Kleisli m a)           instance (Alternative m) => Semigroupal (->) Either (,) (Kleisli m a)
deriving via FromAlternative (Ap f)                  instance (Alternative f) => Semigroupal (->) Either (,) (Ap f)
deriving via FromAlternative (Alt f)                 instance (Alternative f) => Semigroupal (->) Either (,) (Alt f)
deriving via FromAlternative (Rec1 f)                instance (Alternative f) => Semigroupal (->) Either (,) (Rec1 f)
deriving via FromAlternative (Product f g)           instance (Alternative f, Alternative g) => Semigroupal (->) Either (,) (Product f g)
deriving via FromAlternative (f :*: g)               instance (Alternative f, Alternative g) => Semigroupal (->) Either (,) (f :*: g)
deriving via FromAlternative (f `Compose` g)         instance (Alternative f, Applicative g) => Semigroupal (->) Either (,) (f `Compose` g)
deriving via FromAlternative (f :.: g)               instance (Alternative f, Applicative g) => Semigroupal (->) Either (,) (f :.: g)
deriving via FromAlternative (M1 i c f)              instance (Alternative f) => Semigroupal (->) Either (,) (M1 i c f)

newtype FromSemialign f a = FromSemialign (f a)
  deriving newtype (Functor, Semialign)

instance Semialign f => Semigroupal (->) These (,) (FromSemialign f) where
  combine :: (FromSemialign f x, FromSemialign f x') -> FromSemialign f (These x x')
  combine = uncurry align

deriving via FromSemialign []                      instance Semigroupal (->) These (,) []
deriving via FromSemialign ZipList                 instance Semigroupal (->) These (,) ZipList
deriving via FromSemialign NonEmpty                instance Semigroupal (->) These (,) NonEmpty
deriving via FromSemialign Maybe                   instance Semigroupal (->) These (,) Maybe
deriving via FromSemialign Identity                instance Semigroupal (->) These (,) Identity
deriving via FromSemialign (Proxy :: Type -> Type) instance Semigroupal (->) These (,) (Proxy :: Type -> Type)
deriving via FromSemialign (Tagged b)              instance Semigroupal (->) These (,) (Tagged b)
deriving via FromSemialign (Product f g)           instance (Semialign f, Semialign g) => Semigroupal (->) These (,) (Product f g)
deriving via FromSemialign (f `Compose` g)         instance (Semialign f, Semialign g) => Semigroupal (->) These (,) (f `Compose` g)

newtype FromDivisible f a = FromDivisible (f a)
  deriving newtype (Contravariant, Divisible)

instance Divisible f => Semigroupal (->) (,) (,) (FromDivisible f) where 
  combine :: (FromDivisible f x, FromDivisible f x') -> FromDivisible f (x, x')
  combine = uncurry divided

deriving via FromDivisible Predicate               instance Semigroupal (->) (,) (,) Predicate
deriving via FromDivisible Comparison              instance Semigroupal (->) (,) (,) Comparison
deriving via FromDivisible Equivalence             instance Semigroupal (->) (,) (,) Equivalence
deriving via FromDivisible (U1 :: Type -> Type)    instance Semigroupal (->) (,) (,) (U1 :: Type -> Type)
deriving via FromDivisible (Op r)                  instance Monoid r => Semigroupal (->) (,) (,) (Op r)
deriving via FromDivisible (Proxy :: Type -> Type) instance Semigroupal (->) (,) (,) (Proxy :: Type -> Type)
deriving via FromDivisible (MaybeT m)              instance Divisible m => Semigroupal (->) (,) (,) (MaybeT m)
deriving via FromDivisible (Rec1 m)                instance Divisible m => Semigroupal (->) (,) (,) (Rec1 m)
deriving via FromDivisible (Const m)               instance Monoid m => Semigroupal (->) (,) (,) (Const m :: Type -> Type)
deriving via FromDivisible (Alt f)                 instance Divisible f => Semigroupal (->) (,) (,) (Alt f)
deriving via FromDivisible (Reverse f)             instance Divisible f => Semigroupal (->) (,) (,) (Reverse f)
deriving via FromDivisible (Constant m)            instance Monoid m => Semigroupal (->) (,) (,) (Constant m :: Type -> Type)
deriving via FromDivisible (WriterT w m)           instance Divisible m => Semigroupal (->) (,) (,) (WriterT w m)
deriving via FromDivisible (Lazy.WriterT w m)      instance Divisible m => Semigroupal (->) (,) (,) (Lazy.WriterT w m)
deriving via FromDivisible (StateT w m)            instance Divisible m => Semigroupal (->) (,) (,) (StateT w m)
deriving via FromDivisible (Lazy.StateT w m)       instance Divisible m => Semigroupal (->) (,) (,) (Lazy.StateT w m)
deriving via FromDivisible (ReaderT r m)           instance Divisible m => Semigroupal (->) (,) (,) (ReaderT r m)
deriving via FromDivisible (IdentityT m)           instance Divisible m => Semigroupal (->) (,) (,) (IdentityT m)
deriving via FromDivisible (ExceptT e m)           instance Divisible m => Semigroupal (->) (,) (,) (ExceptT e m)
deriving via FromDivisible (Backwards f)           instance Divisible f => Semigroupal (->) (,) (,) (Backwards f)
deriving via FromDivisible (ComposeCF f g)         instance (Divisible f, Applicative g) => Semigroupal (->) (,) (,) (ComposeCF f g)
deriving via FromDivisible (ComposeFC f g)         instance (Divisible g, Applicative f) => Semigroupal (->) (,) (,) (ComposeFC f g)
deriving via FromDivisible (f :*: g)               instance (Divisible f, Divisible g) => Semigroupal (->) (,) (,) (f :*: g)
deriving via FromDivisible (Product f g)           instance (Divisible f, Divisible g) => Semigroupal (->) (,) (,) (Product f g)
deriving via FromDivisible (M1 i c f)              instance Semigroupal (->) (,) (,) (M1 i c f)
deriving via FromDivisible (f :.: g)               instance (Divisible f, Divisible g) => Semigroupal (->) (,) (,) (f :.: g)
deriving via FromDivisible (Compose f g)           instance (Divisible f, Divisible g) => Semigroupal (->) (,) (,) (Compose f g)
deriving via FromDivisible (RWST r w s m)          instance (Divisible m) => Semigroupal (->) (,) (,) (RWST r w s m)
deriving via FromDivisible (Lazy.RWST r w s m)     instance (Divisible m) => Semigroupal (->) (,) (,) (Lazy.RWST r w s m)

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Unital' if it supports a morphism \(\phi : I_{\mathcal{D}} \to F\ I_{\mathcal{C}}\),
-- which we call 'introduce'.
class Unital cat i1 i0 f where
  -- | @introduce@ maps from the identity in \(\mathcal{C}\) to the
  -- identity in \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> introduce @(->) @() @() @Maybe ()
  -- Just ()
  --
  -- >>> :t introduce @(->) @Void @() @Maybe 
  -- introduce @(->) @Void @() @Maybe :: () -> Maybe Void
  -- 
  -- >>> introduce @(->) @Void @() @Maybe ()
  -- Nothing
  introduce :: cat i0 (f i1)

instance Applicative f => Unital (->) () () (FromApplicative f) where
  introduce :: () -> FromApplicative f ()
  introduce = pure

deriving via FromApplicative Identity           instance Unital (->) () () Identity
deriving via FromApplicative (Compose f g)      instance (Applicative f, Applicative g) => Unital (->) () () (Compose f g)
deriving via FromApplicative []                 instance Unital (->) () () []
deriving via FromApplicative ZipList            instance Unital (->) () () ZipList
deriving via FromApplicative NonEmpty           instance Unital (->) () () NonEmpty
deriving via FromApplicative Maybe              instance Unital (->) () () Maybe
deriving via FromApplicative (Either e)         instance Unital (->) () () (Either e)
deriving via FromApplicative IO                 instance Unital (->) () () IO
deriving via FromApplicative (Product f g)      instance (Applicative f, Applicative g) => Unital (->) () () (Product f g)
deriving via (FromApplicative ((,) x1))         instance (Monoid x1) => Unital (->) () () ((,) x1)
deriving via (FromApplicative ((,,) x1 x2))     instance (Monoid x1, Monoid x2) => Unital (->) () () ((,,) x1 x2)
deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Unital (->) () () ((,,,) x1 x2 x3)

instance Alternative f => Unital (->) Void () (FromAlternative f) where
  introduce :: () -> FromAlternative f Void
  introduce () = empty

deriving via FromAlternative ZipList                 instance Unital (->) Void () ZipList
deriving via FromAlternative STM                     instance Unital (->) Void () STM
deriving via FromAlternative ReadP                   instance Unital (->) Void () ReadP
deriving via FromAlternative ReadPrec                instance Unital (->) Void () ReadPrec
deriving via FromAlternative IO                      instance Unital (->) Void () IO
deriving via FromAlternative Maybe                   instance Unital (->) Void () Maybe
deriving via FromAlternative []                      instance Unital (->) Void () []
deriving via FromAlternative (WrappedMonad m)        instance (MonadPlus m) => Unital (->) Void () (WrappedMonad m)
deriving via FromAlternative (ArrowMonad a)          instance (ArrowPlus a) => Unital (->) Void () (ArrowMonad a)
deriving via FromAlternative (Proxy :: Type -> Type) instance Unital (->) Void () (Proxy :: Type -> Type)
deriving via FromAlternative (U1 :: Type -> Type)    instance Unital (->) Void () (U1 :: Type -> Type)
deriving via FromAlternative (WrappedArrow a b)      instance (ArrowZero a, ArrowPlus a) => Unital (->) Void () (WrappedArrow a b)
deriving via FromAlternative (Kleisli m a)           instance (Alternative m) => Unital (->) Void () (Kleisli m a)
deriving via FromAlternative (Ap f)                  instance (Alternative f) => Unital (->) Void () (Ap f)
deriving via FromAlternative (Alt f)                 instance (Alternative f) => Unital (->) Void () (Alt f)
deriving via FromAlternative (Rec1 f)                instance (Alternative f) => Unital (->) Void () (Rec1 f)
deriving via FromAlternative (Product f g)           instance (Alternative f, Alternative g) => Unital (->) Void () (Product f g)
deriving via FromAlternative (f :*: g)               instance (Alternative f, Alternative g) => Unital (->) Void () (f :*: g)
deriving via FromAlternative (f `Compose` g)         instance (Alternative f, Applicative g) => Unital (->) Void () (f `Compose` g)
deriving via FromAlternative (f :.: g)               instance (Alternative f, Applicative g) => Unital (->) Void () (f :.: g)
deriving via FromAlternative (M1 i c f)              instance (Alternative f) => Unital (->) Void () (M1 i c f)

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Monoidal' if it maps between \(\mathcal{C}\) and \(\mathcal{D}\) while
-- preserving their monoidal structure. Eg., a homomorphism of monoidal categories.
--
-- See <https://ncatlab.org/nlab/show/monoidal+functor NCatlab> for more details.
--
-- === Laws
--
-- __Right Unitality__:
--
-- \[ 
-- \require{AMScd}
-- \begin{CD}
-- F A \bullet I_{\mathcal{D}}   @>{1 \bullet \phi}>>         F A \bullet F I_{\mathcal{C}};\\
-- @VV{\rho_{\mathcal{D}}}V                                   @VV{\phi A,I_{\mathcal{C}}}V \\
-- F A                           @<<{F \rho_{\mathcal{C}}}<   F (A \otimes I_{\mathcal{C}});
-- \end{CD}
-- \]
--
-- @
--   'combine' 'Control.Category..' 'grmap' 'introduce' ≡ 'bwd' 'unitr' 'Control.Category..' 'fwd' 'unitr'
-- @
--
-- __ Left Unitality__:
--
-- \[ 
-- \begin{CD}
-- I_{\mathcal{D}} \bullet F B   @>{\phi \bullet 1}>>            F I_{\mathcal{C}} \bullet F B;\\
-- @VV{\lambda_{\mathcal{D}}}V                                   @VV{\phi I_{\mathcal{C}},B}V \\
-- F A                           @<<{F \lambda_{\mathcal{C}}}<   F (A \otimes I_{\mathcal{C}} \otimes B);
-- \end{CD}
-- \]
--
-- @
--   'combine' 'Control.Category..' 'glmap' 'introduce' ≡ 'fmap' ('bwd' 'unitl') 'Control.Category..' 'fwd' 'unitl'
-- @
class
  ( Tensor cat t1 i1
  , Tensor cat t0 i0
  , Semigroupal cat t1 t0 f
  , Unital cat i1 i0 f
  ) => Monoidal cat t1 i1 t0 i0 f

instance Applicative f => Monoidal (->) (,) () (,) () (FromApplicative f)

deriving via FromApplicative Identity           instance Monoidal (->) (,) () (,) () Identity
deriving via FromApplicative (Compose f g)      instance (Applicative f, Applicative g) => Monoidal (->) (,) () (,) () (Compose f g)
deriving via FromApplicative []                 instance Monoidal (->) (,) () (,) () []
deriving via FromApplicative ZipList            instance Monoidal (->) (,) () (,) () ZipList
deriving via FromApplicative NonEmpty           instance Monoidal (->) (,) () (,) () NonEmpty
deriving via FromApplicative Maybe              instance Monoidal (->) (,) () (,) () Maybe
deriving via FromApplicative (Either e)         instance Monoidal (->) (,) () (,) () (Either e)
deriving via FromApplicative IO                 instance Monoidal (->) (,) () (,) () IO
deriving via FromApplicative (Product f g)      instance (Applicative f, Applicative g) => Monoidal (->) (,) () (,) () (Product f g)
deriving via (FromApplicative ((,) x1))         instance (Monoid x1) => Monoidal (->) (,) () (,) () ((,) x1)
deriving via (FromApplicative ((,,) x1 x2))     instance (Monoid x1, Monoid x2) => Monoidal (->) (,) () (,) () ((,,) x1 x2)
deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Monoidal (->) (,) () (,) () ((,,,) x1 x2 x3)

instance Alternative f => Monoidal (->) Either Void (,) () (FromAlternative f)

deriving via FromAlternative ZipList                 instance Monoidal (->) Either Void (,) () ZipList
deriving via FromAlternative STM                     instance Monoidal (->) Either Void (,) () STM
deriving via FromAlternative ReadP                   instance Monoidal (->) Either Void (,) () ReadP
deriving via FromAlternative ReadPrec                instance Monoidal (->) Either Void (,) () ReadPrec
deriving via FromAlternative IO                      instance Monoidal (->) Either Void (,) () IO
deriving via FromAlternative Maybe                   instance Monoidal (->) Either Void (,) () Maybe
deriving via FromAlternative []                      instance Monoidal (->) Either Void (,) () []
deriving via FromAlternative (WrappedMonad m)        instance (MonadPlus m) => Monoidal (->) Either Void (,) () (WrappedMonad m)
deriving via FromAlternative (ArrowMonad a)          instance (ArrowPlus a) => Monoidal (->) Either Void (,) () (ArrowMonad a)
deriving via FromAlternative (Proxy :: Type -> Type) instance Monoidal (->) Either Void (,) () (Proxy :: Type -> Type)
deriving via FromAlternative (U1 :: Type -> Type)    instance Monoidal (->) Either Void (,) () (U1 :: Type -> Type)
deriving via FromAlternative (WrappedArrow a b)      instance (ArrowZero a, ArrowPlus a) => Monoidal (->) Either Void (,) () (WrappedArrow a b)
deriving via FromAlternative (Kleisli m a)           instance (Alternative m) => Monoidal (->) Either Void (,) () (Kleisli m a)
deriving via FromAlternative (Ap f)                  instance (Alternative f) => Monoidal (->) Either Void (,) () (Ap f)
deriving via FromAlternative (Alt f)                 instance (Alternative f) => Monoidal (->) Either Void (,) () (Alt f)
deriving via FromAlternative (Rec1 f)                instance (Alternative f) => Monoidal (->) Either Void (,) () (Rec1 f)
deriving via FromAlternative (Product f g)           instance (Alternative f, Alternative g) => Monoidal (->) Either Void (,) () (Product f g)
deriving via FromAlternative (f :*: g)               instance (Alternative f, Alternative g) => Monoidal (->) Either Void (,) () (f :*: g)
deriving via FromAlternative (f `Compose` g)         instance (Alternative f, Applicative g) => Monoidal (->) Either Void (,) () (f `Compose` g)
deriving via FromAlternative (f :.: g)               instance (Alternative f, Applicative g) => Monoidal (->) Either Void (,) () (f :.: g)
deriving via FromAlternative (M1 i c f)              instance (Alternative f) => Monoidal (->) Either Void (,) () (M1 i c f)
