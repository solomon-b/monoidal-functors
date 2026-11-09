{-# LANGUAGE CPP #-}

module Data.Functor.Monoidal
  ( -- * Semigroupal
    Semigroupal (..),
    (|?|),
    (|*|),
    (|+|),
    (|&|),

    -- * Unital
    Unital (..),

    -- * Monoidal
    Monoidal,

    -- * Newtypes for Deriving Via
    FromApplicative (..),
    FromAlternative (..),
    FromSemialign (..),
    FromDivisible (..),
    FromDecidable (..),
    FromUnalign (..),
    FromAlign (..),
  )
where

--------------------------------------------------------------------------------

import Control.Applicative
import Control.Applicative.Backwards (Backwards (..))
import Control.Arrow (ArrowMonad, ArrowPlus, ArrowZero, Kleisli)
import Control.Category.Tensor
import Control.Comonad.Identity (IdentityT)
import Control.Monad (MonadPlus)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.RWS.Lazy qualified as Lazy
import Control.Monad.Trans.RWS.Strict (RWST)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State.Lazy qualified as Lazy
import Control.Monad.Trans.State.Strict (StateT)
import Control.Monad.Trans.Writer.Lazy qualified as Lazy
import Control.Monad.Trans.Writer.Strict (WriterT)
import Data.Align
import Data.Functor.Compose (Compose)
#if MIN_VERSION_semialign(1,4,0)
import Data.Zip (Unzip)
#endif
import Data.Functor.Constant (Constant (..))
import Data.Functor.Contravariant (Comparison, Contravariant, Equivalence, Op (..), Predicate)
import Data.Functor.Contravariant.Compose (ComposeCF, ComposeFC)
import Data.Functor.Contravariant.Divisible (Decidable, Divisible, chosen, conquered, divided, lost)
import Data.Functor.Identity
import Data.Functor.Product (Product (Pair))
import Data.Functor.Reverse (Reverse (..))
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid (Alt (..), Ap)
import Data.Proxy (Proxy (..))
import Data.Tagged (Tagged)
import Data.These
import Data.Void
import GHC.Conc (STM)
import GHC.Generics (M1 (..), Rec1 (..), U1 (..), type (:*:) (..), type (:.:))
import Text.ParserCombinators.ReadP (ReadP)
import Text.ParserCombinators.ReadPrec (ReadPrec)
import Prelude

--------------------------------------------------------------------------------

-- $setup
-- >>> :set -dppr-cols=1000
-- >>> import Prelude
-- >>> import Data.Void (Void)

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
class (Associative cat tC, Associative cat tD) => Semigroupal cat tC tD f where
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
  combine :: (f x `tD` f x') `cat` f (x `tC` x')

newtype FromApplicative f a = FromApplicative (f a)
  deriving newtype (Functor, Applicative)

instance (Applicative f) => Semigroupal (->) (,) (,) (FromApplicative f) where
  combine :: (FromApplicative f x, FromApplicative f x') -> FromApplicative f (x, x')
  combine = uncurry (liftA2 (,))

deriving via FromApplicative Identity instance Semigroupal (->) (,) (,) Identity

instance Semigroupal Op Either Either Identity where
  combine :: Op (Either (Identity x) (Identity x')) (Identity (Either x x'))
  combine = Op $ \case
    Identity (Left x) -> Left $ Identity x
    Identity (Right x') -> Right $ Identity x'

deriving via FromApplicative (Compose f g) instance (Applicative f, Applicative g) => Semigroupal (->) (,) (,) (Compose f g)

deriving via FromApplicative [] instance Semigroupal (->) (,) (,) []

deriving via FromApplicative ZipList instance Semigroupal (->) (,) (,) ZipList

deriving via FromApplicative NonEmpty instance Semigroupal (->) (,) (,) NonEmpty

deriving via FromApplicative Maybe instance Semigroupal (->) (,) (,) Maybe

deriving via FromApplicative (Either e) instance Semigroupal (->) (,) (,) (Either e)

deriving via FromApplicative IO instance Semigroupal (->) (,) (,) IO

-- | A single variance-agnostic 'Product' instance. @combine@ is componentwise,
-- delegating to each component's own 'Semigroupal'. It subsumes the former
-- @FromApplicative@ \/ @FromAlternative@ \/ @FromSemialign@ instances (product,
-- coproduct, and these tensors) and covers the contravariant components
-- (Divisible \/ Decidable), which previously overlapped.
instance (Semigroupal (->) tC (,) f, Semigroupal (->) tC (,) g) => Semigroupal (->) tC (,) (Product f g) where
  combine :: forall x x'. (Product f g x, Product f g x') -> Product f g (tC x x')
  combine (Pair fx gx, Pair fx' gx') =
    Pair (combine @(->) @tC @(,) (fx, fx')) (combine @(->) @tC @(,) (gx, gx'))

deriving via (FromApplicative ((,) x1)) instance (Monoid x1) => Semigroupal (->) (,) (,) ((,) x1)

deriving via (FromApplicative ((,,) x1 x2)) instance (Monoid x1, Monoid x2) => Semigroupal (->) (,) (,) ((,,) x1 x2)

deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Semigroupal (->) (,) (,) ((,,,) x1 x2 x3)

newtype FromAlternative f a = FromAlternative (f a)
  deriving newtype (Functor, Applicative, Alternative)

instance (Alternative f) => Semigroupal (->) Either (,) (FromAlternative f) where
  combine :: (FromAlternative f x, FromAlternative f x') -> FromAlternative f (Either x x')
  combine (fx, fx') = fmap Left fx <|> fmap Right fx'

deriving via FromAlternative ZipList instance Semigroupal (->) Either (,) ZipList

deriving via FromAlternative STM instance Semigroupal (->) Either (,) STM

deriving via FromAlternative ReadP instance Semigroupal (->) Either (,) ReadP

deriving via FromAlternative ReadPrec instance Semigroupal (->) Either (,) ReadPrec

deriving via FromAlternative IO instance Semigroupal (->) Either (,) IO

deriving via FromAlternative Maybe instance Semigroupal (->) Either (,) Maybe

deriving via FromAlternative [] instance Semigroupal (->) Either (,) []

deriving via FromAlternative (WrappedMonad m) instance (MonadPlus m) => Semigroupal (->) Either (,) (WrappedMonad m)

deriving via FromAlternative (ArrowMonad a) instance (ArrowPlus a) => Semigroupal (->) Either (,) (ArrowMonad a)

deriving via FromAlternative (WrappedArrow a b) instance (ArrowZero a, ArrowPlus a) => Semigroupal (->) Either (,) (WrappedArrow a b)

deriving via FromAlternative (Kleisli m a) instance (Alternative m) => Semigroupal (->) Either (,) (Kleisli m a)

deriving via FromAlternative (Ap f) instance (Alternative f) => Semigroupal (->) Either (,) (Ap f)

-- | A transparent newtype wrapper inherits its component's 'Semigroupal' at
-- every tensor and both variances, by coercion.
deriving newtype instance (Semigroupal (->) tC (,) f) => Semigroupal (->) tC (,) (Rec1 f)

deriving newtype instance (Semigroupal (->) tC (,) f) => Semigroupal (->) tC (,) (M1 i c f)

deriving newtype instance (Semigroupal (->) tC (,) f) => Semigroupal (->) tC (,) (Alt f)

deriving newtype instance (Semigroupal (->) tC (,) f) => Semigroupal (->) tC (,) (Reverse f)

deriving newtype instance (Semigroupal (->) tC (,) f) => Semigroupal (->) tC (,) (Backwards f)

-- | Componentwise, like 'Product'. The generic product @f ':*:' g@ is
-- 'Semigroupal' at any tensor its components share, both variances.
instance (Semigroupal (->) tC (,) f, Semigroupal (->) tC (,) g) => Semigroupal (->) tC (,) (f :*: g) where
  combine :: forall x x'. ((f :*: g) x, (f :*: g) x') -> (f :*: g) (tC x x')
  combine (fx :*: gx, fx' :*: gx') =
    combine @(->) @tC @(,) (fx, fx') :*: combine @(->) @tC @(,) (gx, gx')

-- | Phantom (constant) functors are both covariant and contravariant at once.
-- @combine@ ignores the parameter, so one instance serves every tensor and both
-- variances. For 'Const' \/ 'Constant' it is the underlying 'Semigroup'.
instance (Associative (->) tC) => Semigroupal (->) tC (,) (Proxy :: Type -> Type) where
  combine _ = Proxy

instance (Associative (->) tC) => Semigroupal (->) tC (,) (U1 :: Type -> Type) where
  combine _ = U1

instance (Semigroup c, Associative (->) tC) => Semigroupal (->) tC (,) (Const c :: Type -> Type) where
  combine (Const a, Const b) = Const (a <> b)

instance (Semigroup c, Associative (->) tC) => Semigroupal (->) tC (,) (Constant c :: Type -> Type) where
  combine (Constant a, Constant b) = Constant (a <> b)

deriving via FromAlternative (f `Compose` g) instance (Alternative f, Applicative g) => Semigroupal (->) Either (,) (f `Compose` g)

deriving via FromAlternative (f :.: g) instance (Alternative f, Applicative g) => Semigroupal (->) Either (,) (f :.: g)

newtype FromSemialign f a = FromSemialign (f a)
#if MIN_VERSION_semialign(1,4,0)
  deriving newtype (Functor, Unzip, Semialign)
#else
  deriving newtype (Functor, Semialign)
#endif

instance (Semialign f) => Semigroupal (->) These (,) (FromSemialign f) where
  combine :: (FromSemialign f x, FromSemialign f x') -> FromSemialign f (These x x')
  combine = uncurry align

deriving via FromSemialign [] instance Semigroupal (->) These (,) []

deriving via FromSemialign ZipList instance Semigroupal (->) These (,) ZipList

deriving via FromSemialign NonEmpty instance Semigroupal (->) These (,) NonEmpty

deriving via FromSemialign Maybe instance Semigroupal (->) These (,) Maybe

deriving via FromSemialign Identity instance Semigroupal (->) These (,) Identity

deriving via FromSemialign (Tagged b) instance Semigroupal (->) These (,) (Tagged b)

deriving via FromSemialign (f `Compose` g) instance (Semialign f, Semialign g) => Semigroupal (->) These (,) (f `Compose` g)

newtype FromDivisible f a = FromDivisible (f a)
  deriving newtype (Contravariant, Divisible)

instance (Divisible f) => Semigroupal (->) (,) (,) (FromDivisible f) where
  combine :: (FromDivisible f x, FromDivisible f x') -> FromDivisible f (x, x')
  combine = uncurry divided

deriving via FromDivisible Predicate instance Semigroupal (->) (,) (,) Predicate

deriving via FromDivisible Comparison instance Semigroupal (->) (,) (,) Comparison

deriving via FromDivisible Equivalence instance Semigroupal (->) (,) (,) Equivalence

deriving via FromDivisible (Op r) instance (Monoid r) => Semigroupal (->) (,) (,) (Op r)

deriving via FromDivisible (MaybeT m) instance (Divisible m) => Semigroupal (->) (,) (,) (MaybeT m)

deriving via FromDivisible (WriterT w m) instance (Divisible m) => Semigroupal (->) (,) (,) (WriterT w m)

deriving via FromDivisible (Lazy.WriterT w m) instance (Divisible m) => Semigroupal (->) (,) (,) (Lazy.WriterT w m)

deriving via FromDivisible (StateT w m) instance (Divisible m) => Semigroupal (->) (,) (,) (StateT w m)

deriving via FromDivisible (Lazy.StateT w m) instance (Divisible m) => Semigroupal (->) (,) (,) (Lazy.StateT w m)

deriving via FromDivisible (ReaderT r m) instance (Divisible m) => Semigroupal (->) (,) (,) (ReaderT r m)

deriving via FromDivisible (IdentityT m) instance (Divisible m) => Semigroupal (->) (,) (,) (IdentityT m)

deriving via FromDivisible (ExceptT e m) instance (Divisible m) => Semigroupal (->) (,) (,) (ExceptT e m)

deriving via FromDivisible (ComposeCF f g) instance (Divisible f, Applicative g) => Semigroupal (->) (,) (,) (ComposeCF f g)

deriving via FromDivisible (ComposeFC f g) instance (Divisible g, Applicative f) => Semigroupal (->) (,) (,) (ComposeFC f g)

deriving via FromDivisible (f :.: g) instance (Applicative f, Divisible g) => Semigroupal (->) (,) (,) (f :.: g)

-- deriving via FromDivisible (Compose f g)           instance (Applicative f, Divisible g) => Semigroupal (->) (,) (,) (Compose f g)
deriving via FromDivisible (RWST r w s m) instance (Divisible m) => Semigroupal (->) (,) (,) (RWST r w s m)

deriving via FromDivisible (Lazy.RWST r w s m) instance (Divisible m) => Semigroupal (->) (,) (,) (Lazy.RWST r w s m)

newtype FromDecidable f a = FromDecidable (f a)
  deriving newtype (Contravariant, Divisible, Decidable)

instance (Decidable f) => Semigroupal (->) Either (,) (FromDecidable f) where
  combine :: (FromDecidable f x, FromDecidable f x') -> FromDecidable f (Either x x')
  combine = uncurry chosen

deriving via FromDecidable Predicate instance Semigroupal (->) Either (,) Predicate

deriving via FromDecidable Comparison instance Semigroupal (->) Either (,) Comparison

deriving via FromDecidable Equivalence instance Semigroupal (->) Either (,) Equivalence

deriving via FromDecidable (Op r) instance (Monoid r) => Semigroupal (->) Either (,) (Op r)

deriving via FromDecidable (MaybeT m) instance (Decidable m) => Semigroupal (->) Either (,) (MaybeT m)

deriving via FromDecidable (WriterT w m) instance (Decidable m) => Semigroupal (->) Either (,) (WriterT w m)

deriving via FromDecidable (Lazy.WriterT w m) instance (Decidable m) => Semigroupal (->) Either (,) (Lazy.WriterT w m)

deriving via FromDecidable (StateT w m) instance (Decidable m) => Semigroupal (->) Either (,) (StateT w m)

deriving via FromDecidable (Lazy.StateT w m) instance (Decidable m) => Semigroupal (->) Either (,) (Lazy.StateT w m)

deriving via FromDecidable (ReaderT r m) instance (Decidable m) => Semigroupal (->) Either (,) (ReaderT r m)

deriving via FromDecidable (IdentityT m) instance (Decidable m) => Semigroupal (->) Either (,) (IdentityT m)

deriving via FromDecidable (ComposeFC f g) instance (Decidable g, Applicative f) => Semigroupal (->) Either (,) (ComposeFC f g)

-- deriving via FromDecidable (f :.: g)               instance (Applicative f, Decidable g) => Semigroupal (->) Either (,) (f :.: g)
-- deriving via FromDecidable (Compose f g)           instance (Applicative f, Decidable g) => Semigroupal (->) Either (,) (Compose f g)
deriving via FromDecidable (RWST r w s m) instance (Decidable m) => Semigroupal (->) Either (,) (RWST r w s m)

deriving via FromDecidable (Lazy.RWST r w s m) instance (Decidable m) => Semigroupal (->) Either (,) (Lazy.RWST r w s m)

newtype FromUnalign f a = FromUnalign (f a)
#if MIN_VERSION_semialign(1,4,0)
  deriving (Functor, Unzip, Semialign, Unalign)
#else
  deriving (Functor, Semialign, Unalign)
#endif

instance (Unalign f) => Semigroupal Op These (,) (FromUnalign f) where
  combine :: Op (FromUnalign f x, FromUnalign f x') (FromUnalign f (These x x'))
  combine = Op unalign

deriving via FromUnalign Maybe instance Semigroupal Op These (,) Maybe

deriving via FromUnalign (Proxy :: Type -> Type) instance Semigroupal Op These (,) (Proxy :: Type -> Type)

deriving via FromUnalign (Product f g) instance (Unalign f, Unalign g) => Semigroupal Op These (,) (Product f g)

infixr 9 |?|

(|?|) :: (Semigroupal (->) tC (,) f) => f a -> f b -> f (a `tC` b)
(|?|) = curry combine

infixr 4 |*|

(|*|) :: (Semigroupal (->) (,) (,) f) => f a -> f b -> f (a, b)
(|*|) = curry combine

infixr 3 |+|

(|+|) :: (Semigroupal (->) Either (,) f) => f a -> f b -> f (Either a b)
(|+|) = curry combine

infixr 3 |&|

(|&|) :: (Semigroupal (->) These (,) f) => f a -> f b -> f (These a b)
(|&|) = curry combine

--------------------------------------------------------------------------------

-- | Given monoidal categories \((\mathcal{C}, \otimes, I_{\mathcal{C}})\) and \((\mathcal{D}, \bullet, I_{\mathcal{D}})\).
-- A functor \(F : \mathcal{C} \to \mathcal{D}\) is 'Unital' if it supports a morphism \(\phi : I_{\mathcal{D}} \to F\ I_{\mathcal{C}}\),
-- which we call 'introduce'.
class Unital cat iC iD f where
  -- | @introduce@ maps from the identity in \(\mathcal{C}\) to the
  -- identity in \(\mathcal{D}\).
  --
  -- ==== __Examples__
  --
  -- >>> introduce @(->) @() @() @Maybe ()
  -- Just ()
  --
  -- >>> introduce @(->) @Void @() @Maybe ()
  -- Nothing
  introduce :: cat iD (f iC)

instance (Applicative f) => Unital (->) () () (FromApplicative f) where
  introduce :: () -> FromApplicative f ()
  introduce = pure

deriving via FromApplicative Identity instance Unital (->) () () Identity

deriving via FromApplicative (Compose f g) instance (Applicative f, Applicative g) => Unital (->) () () (Compose f g)

deriving via FromApplicative [] instance Unital (->) () () []

deriving via FromApplicative ZipList instance Unital (->) () () ZipList

deriving via FromApplicative NonEmpty instance Unital (->) () () NonEmpty

deriving via FromApplicative Maybe instance Unital (->) () () Maybe

deriving via FromApplicative (Either e) instance Unital (->) () () (Either e)

deriving via FromApplicative IO instance Unital (->) () () IO

-- | Componentwise 'introduce', delegating to each component's 'Unital'. Covers
-- both the product unit @()@ and the coproduct unit @Void@, covariant and
-- contravariant alike.
instance (Unital (->) iC () f, Unital (->) iC () g) => Unital (->) iC () (Product f g) where
  introduce :: () -> Product f g iC
  introduce () = Pair (introduce @(->) @iC @() ()) (introduce @(->) @iC @() ())

deriving via (FromApplicative ((,) x1)) instance (Monoid x1) => Unital (->) () () ((,) x1)

deriving via (FromApplicative ((,,) x1 x2)) instance (Monoid x1, Monoid x2) => Unital (->) () () ((,,) x1 x2)

deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Unital (->) () () ((,,,) x1 x2 x3)

instance (Alternative f) => Unital (->) Void () (FromAlternative f) where
  introduce :: () -> FromAlternative f Void
  introduce () = empty

deriving via FromAlternative ZipList instance Unital (->) Void () ZipList

deriving via FromAlternative STM instance Unital (->) Void () STM

deriving via FromAlternative ReadP instance Unital (->) Void () ReadP

deriving via FromAlternative ReadPrec instance Unital (->) Void () ReadPrec

deriving via FromAlternative IO instance Unital (->) Void () IO

deriving via FromAlternative Maybe instance Unital (->) Void () Maybe

deriving via FromAlternative [] instance Unital (->) Void () []

deriving via FromAlternative (WrappedMonad m) instance (MonadPlus m) => Unital (->) Void () (WrappedMonad m)

deriving via FromAlternative (ArrowMonad a) instance (ArrowPlus a) => Unital (->) Void () (ArrowMonad a)

deriving via FromAlternative (WrappedArrow a b) instance (ArrowZero a, ArrowPlus a) => Unital (->) Void () (WrappedArrow a b)

deriving via FromAlternative (Kleisli m a) instance (Alternative m) => Unital (->) Void () (Kleisli m a)

deriving via FromAlternative (Ap f) instance (Alternative f) => Unital (->) Void () (Ap f)

deriving newtype instance (Unital (->) iC () f) => Unital (->) iC () (Rec1 f)

deriving newtype instance (Unital (->) iC () f) => Unital (->) iC () (M1 i c f)

deriving newtype instance (Unital (->) iC () f) => Unital (->) iC () (Alt f)

deriving newtype instance (Unital (->) iC () f) => Unital (->) iC () (Reverse f)

deriving newtype instance (Unital (->) iC () f) => Unital (->) iC () (Backwards f)

instance (Unital (->) iC () f, Unital (->) iC () g) => Unital (->) iC () (f :*: g) where
  introduce :: () -> (f :*: g) iC
  introduce () = introduce @(->) @iC @() () :*: introduce @(->) @iC @() ()

instance Unital (->) iC () (Proxy :: Type -> Type) where
  introduce _ = Proxy

instance Unital (->) iC () (U1 :: Type -> Type) where
  introduce _ = U1

instance (Monoid c) => Unital (->) iC () (Const c :: Type -> Type) where
  introduce _ = Const mempty

instance (Monoid c) => Unital (->) iC () (Constant c :: Type -> Type) where
  introduce _ = Constant mempty

deriving via FromAlternative (f `Compose` g) instance (Alternative f, Applicative g) => Unital (->) Void () (f `Compose` g)

deriving via FromAlternative (f :.: g) instance (Alternative f, Applicative g) => Unital (->) Void () (f :.: g)

newtype FromAlign f a = FromAlign (f a)
#if MIN_VERSION_semialign(1,4,0)
  deriving (Functor, Unzip, Semialign, Align)
#else
  deriving (Functor, Semialign, Align)
#endif

instance (Align f) => Unital (->) Void () (FromAlign f) where
  introduce :: (Align f) => () -> FromAlign f Void
  introduce () = FromAlign nil

-- deriving via FromAlign [] instance Unital (->) Void () []

-- deriving via FromAlign Maybe instance Unital (->) Void () Maybe

-- deriving via FromAlign ZipList instance Unital (->) Void () ZipList

-- deriving via FromAlign (Compose f g) instance (Align f, Semialign g) => Unital (->) Void () (Compose f g)

instance (Divisible f) => Unital (->) () () (FromDivisible f) where
  introduce :: () -> FromDivisible f ()
  introduce () = FromDivisible conquered

deriving via FromDivisible Predicate instance Unital (->) () () Predicate

deriving via FromDivisible Comparison instance Unital (->) () () Comparison

deriving via FromDivisible Equivalence instance Unital (->) () () Equivalence

deriving via FromDivisible (Op r) instance (Monoid r) => Unital (->) () () (Op r)

deriving via FromDivisible (MaybeT m) instance (Divisible m) => Unital (->) () () (MaybeT m)

deriving via FromDivisible (WriterT w m) instance (Divisible m) => Unital (->) () () (WriterT w m)

deriving via FromDivisible (Lazy.WriterT w m) instance (Divisible m) => Unital (->) () () (Lazy.WriterT w m)

deriving via FromDivisible (StateT w m) instance (Divisible m) => Unital (->) () () (StateT w m)

deriving via FromDivisible (Lazy.StateT w m) instance (Divisible m) => Unital (->) () () (Lazy.StateT w m)

deriving via FromDivisible (ReaderT r m) instance (Divisible m) => Unital (->) () () (ReaderT r m)

deriving via FromDivisible (IdentityT m) instance (Divisible m) => Unital (->) () () (IdentityT m)

deriving via FromDivisible (ExceptT e m) instance (Divisible m) => Unital (->) () () (ExceptT e m)

deriving via FromDivisible (ComposeCF f g) instance (Divisible f, Applicative g) => Unital (->) () () (ComposeCF f g)

deriving via FromDivisible (ComposeFC f g) instance (Divisible g, Applicative f) => Unital (->) () () (ComposeFC f g)

deriving via FromDivisible (f :.: g) instance (Applicative f, Divisible g) => Unital (->) () () (f :.: g)

-- deriving via FromDivisible (Compose f g)           instance (Applicative f, Divisible g) => Unital (->) () () (Compose f g)
deriving via FromDivisible (RWST r w s m) instance (Divisible m) => Unital (->) () () (RWST r w s m)

deriving via FromDivisible (Lazy.RWST r w s m) instance (Divisible m) => Unital (->) () () (Lazy.RWST r w s m)

instance (Decidable f) => Unital (->) Void () (FromDecidable f) where
  introduce :: () -> FromDecidable f Void
  introduce () = FromDecidable lost

deriving via FromDecidable Predicate instance Unital (->) Void () Predicate

deriving via FromDecidable Comparison instance Unital (->) Void () Comparison

deriving via FromDecidable Equivalence instance Unital (->) Void () Equivalence

deriving via FromDecidable (Op r) instance (Monoid r) => Unital (->) Void () (Op r)

deriving via FromDecidable (MaybeT m) instance (Decidable m) => Unital (->) Void () (MaybeT m)

deriving via FromDecidable (WriterT w m) instance (Decidable m) => Unital (->) Void () (WriterT w m)

deriving via FromDecidable (Lazy.WriterT w m) instance (Decidable m) => Unital (->) Void () (Lazy.WriterT w m)

deriving via FromDecidable (StateT w m) instance (Decidable m) => Unital (->) Void () (StateT w m)

deriving via FromDecidable (Lazy.StateT w m) instance (Decidable m) => Unital (->) Void () (Lazy.StateT w m)

deriving via FromDecidable (ReaderT r m) instance (Decidable m) => Unital (->) Void () (ReaderT r m)

deriving via FromDecidable (IdentityT m) instance (Decidable m) => Unital (->) Void () (IdentityT m)

deriving via FromDecidable (ComposeFC f g) instance (Decidable g, Applicative f) => Unital (->) Void () (ComposeFC f g)

-- deriving via FromDecidable (f :.: g)               instance (Applicative f, Decidable g) => Unital (->) Void () (f :.: g)
-- deriving via FromDecidable (Compose f g)           instance (Applicative f, Decidable g) => Unital (->) Void () (Compose f g)
deriving via FromDecidable (RWST r w s m) instance (Decidable m) => Unital (->) Void () (RWST r w s m)

deriving via FromDecidable (Lazy.RWST r w s m) instance (Decidable m) => Unital (->) Void () (Lazy.RWST r w s m)

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
  ( Tensor cat tC iC,
    Tensor cat tD iD,
    Semigroupal cat tC tD f,
    Unital cat iC iD f
  ) =>
  Monoidal cat tC iC tD iD f

instance (Applicative f) => Monoidal (->) (,) () (,) () (FromApplicative f)

deriving via FromApplicative Identity instance Monoidal (->) (,) () (,) () Identity

deriving via FromApplicative (Compose f g) instance (Applicative f, Applicative g) => Monoidal (->) (,) () (,) () (Compose f g)

deriving via FromApplicative [] instance Monoidal (->) (,) () (,) () []

deriving via FromApplicative ZipList instance Monoidal (->) (,) () (,) () ZipList

deriving via FromApplicative NonEmpty instance Monoidal (->) (,) () (,) () NonEmpty

deriving via FromApplicative Maybe instance Monoidal (->) (,) () (,) () Maybe

deriving via FromApplicative (Either e) instance Monoidal (->) (,) () (,) () (Either e)

deriving via FromApplicative IO instance Monoidal (->) (,) () (,) () IO

instance (Semigroupal (->) tC (,) f, Semigroupal (->) tC (,) g, Unital (->) iC () f, Unital (->) iC () g, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Product f g)

deriving via (FromApplicative ((,) x1)) instance (Monoid x1) => Monoidal (->) (,) () (,) () ((,) x1)

deriving via (FromApplicative ((,,) x1 x2)) instance (Monoid x1, Monoid x2) => Monoidal (->) (,) () (,) () ((,,) x1 x2)

deriving via (FromApplicative ((,,,) x1 x2 x3)) instance (Monoid x1, Monoid x2, Monoid x3) => Monoidal (->) (,) () (,) () ((,,,) x1 x2 x3)

instance (Alternative f) => Monoidal (->) Either Void (,) () (FromAlternative f)

deriving via FromAlternative ZipList instance Monoidal (->) Either Void (,) () ZipList

deriving via FromAlternative STM instance Monoidal (->) Either Void (,) () STM

deriving via FromAlternative ReadP instance Monoidal (->) Either Void (,) () ReadP

deriving via FromAlternative ReadPrec instance Monoidal (->) Either Void (,) () ReadPrec

deriving via FromAlternative IO instance Monoidal (->) Either Void (,) () IO

deriving via FromAlternative Maybe instance Monoidal (->) Either Void (,) () Maybe

deriving via FromAlternative [] instance Monoidal (->) Either Void (,) () []

deriving via FromAlternative (WrappedMonad m) instance (MonadPlus m) => Monoidal (->) Either Void (,) () (WrappedMonad m)

deriving via FromAlternative (ArrowMonad a) instance (ArrowPlus a) => Monoidal (->) Either Void (,) () (ArrowMonad a)

deriving via FromAlternative (WrappedArrow a b) instance (ArrowZero a, ArrowPlus a) => Monoidal (->) Either Void (,) () (WrappedArrow a b)

deriving via FromAlternative (Kleisli m a) instance (Alternative m) => Monoidal (->) Either Void (,) () (Kleisli m a)

deriving via FromAlternative (Ap f) instance (Alternative f) => Monoidal (->) Either Void (,) () (Ap f)

instance (Semigroupal (->) tC (,) f, Unital (->) iC () f, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Rec1 f)

instance (Semigroupal (->) tC (,) f, Unital (->) iC () f, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (M1 i c f)

instance (Semigroupal (->) tC (,) f, Unital (->) iC () f, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Alt f)

instance (Semigroupal (->) tC (,) f, Unital (->) iC () f, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Reverse f)

instance (Semigroupal (->) tC (,) f, Unital (->) iC () f, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Backwards f)

instance (Semigroupal (->) tC (,) f, Semigroupal (->) tC (,) g, Unital (->) iC () f, Unital (->) iC () g, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (f :*: g)

instance (Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Proxy :: Type -> Type)

instance (Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (U1 :: Type -> Type)

instance (Monoid c, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Const c :: Type -> Type)

instance (Monoid c, Tensor (->) tC iC) => Monoidal (->) tC iC (,) () (Constant c :: Type -> Type)

deriving via FromAlternative (f `Compose` g) instance (Alternative f, Applicative g) => Monoidal (->) Either Void (,) () (f `Compose` g)

deriving via FromAlternative (f :.: g) instance (Alternative f, Applicative g) => Monoidal (->) Either Void (,) () (f :.: g)

deriving via FromDivisible Predicate instance Monoidal (->) (,) () (,) () Predicate

deriving via FromDivisible Comparison instance Monoidal (->) (,) () (,) () Comparison

deriving via FromDivisible Equivalence instance Monoidal (->) (,) () (,) () Equivalence

deriving via FromDivisible (Op r) instance (Monoid r) => Monoidal (->) (,) () (,) () (Op r)

deriving via FromDivisible (MaybeT m) instance (Divisible m) => Monoidal (->) (,) () (,) () (MaybeT m)

deriving via FromDivisible (WriterT w m) instance (Divisible m) => Monoidal (->) (,) () (,) () (WriterT w m)

deriving via FromDivisible (Lazy.WriterT w m) instance (Divisible m) => Monoidal (->) (,) () (,) () (Lazy.WriterT w m)

deriving via FromDivisible (StateT w m) instance (Divisible m) => Monoidal (->) (,) () (,) () (StateT w m)

deriving via FromDivisible (Lazy.StateT w m) instance (Divisible m) => Monoidal (->) (,) () (,) () (Lazy.StateT w m)

deriving via FromDivisible (ReaderT r m) instance (Divisible m) => Monoidal (->) (,) () (,) () (ReaderT r m)

deriving via FromDivisible (IdentityT m) instance (Divisible m) => Monoidal (->) (,) () (,) () (IdentityT m)

deriving via FromDivisible (ExceptT e m) instance (Divisible m) => Monoidal (->) (,) () (,) () (ExceptT e m)

deriving via FromDivisible (ComposeCF f g) instance (Divisible f, Applicative g) => Monoidal (->) (,) () (,) () (ComposeCF f g)

deriving via FromDivisible (ComposeFC f g) instance (Divisible g, Applicative f) => Monoidal (->) (,) () (,) () (ComposeFC f g)

deriving via FromDivisible (f :.: g) instance (Applicative f, Divisible g) => Monoidal (->) (,) () (,) () (f :.: g)

-- deriving via FromDivisible (Compose f g)           instance (Applicative f, Divisible g) => Monoidal (->) (,) () (,) () (Compose f g)
deriving via FromDivisible (RWST r w s m) instance (Divisible m) => Monoidal (->) (,) () (,) () (RWST r w s m)

deriving via FromDivisible (Lazy.RWST r w s m) instance (Divisible m) => Monoidal (->) (,) () (,) () (Lazy.RWST r w s m)

deriving via FromDecidable Predicate instance Monoidal (->) Either Void (,) () Predicate

deriving via FromDecidable Comparison instance Monoidal (->) Either Void (,) () Comparison

deriving via FromDecidable Equivalence instance Monoidal (->) Either Void (,) () Equivalence

deriving via FromDecidable (Op r) instance (Monoid r) => Monoidal (->) Either Void (,) () (Op r)

deriving via FromDecidable (MaybeT m) instance (Decidable m) => Monoidal (->) Either Void (,) () (MaybeT m)

deriving via FromDecidable (WriterT w m) instance (Decidable m) => Monoidal (->) Either Void (,) () (WriterT w m)

deriving via FromDecidable (Lazy.WriterT w m) instance (Decidable m) => Monoidal (->) Either Void (,) () (Lazy.WriterT w m)

deriving via FromDecidable (StateT w m) instance (Decidable m) => Monoidal (->) Either Void (,) () (StateT w m)

deriving via FromDecidable (Lazy.StateT w m) instance (Decidable m) => Monoidal (->) Either Void (,) () (Lazy.StateT w m)

deriving via FromDecidable (ReaderT r m) instance (Decidable m) => Monoidal (->) Either Void (,) () (ReaderT r m)

deriving via FromDecidable (IdentityT m) instance (Decidable m) => Monoidal (->) Either Void (,) () (IdentityT m)

deriving via FromDecidable (ComposeFC f g) instance (Decidable g, Applicative f) => Monoidal (->) Either Void (,) () (ComposeFC f g)

-- deriving via FromDecidable (f :.: g)               instance (Applicative f, Decidable g) => Monoidal (->) Either Void (,) () (f :.: g)
-- deriving via FromDecidable (Compose f g)           instance (Applicative f, Decidable g) => Monoidal (->) Either Void (,) () (Compose f g)
deriving via FromDecidable (RWST r w s m) instance (Decidable m) => Monoidal (->) Either Void (,) () (RWST r w s m)

deriving via FromDecidable (Lazy.RWST r w s m) instance (Decidable m) => Monoidal (->) Either Void (,) () (Lazy.RWST r w s m)
