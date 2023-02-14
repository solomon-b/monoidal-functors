module Main where

--------------------------------------------------------------------------------

import Control.Category
import Control.Category.Cartesian
import Control.Category.Tensor
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.Trans
import Data.Coerce
import Data.Functor.Contravariant hiding ((>$<))
import Data.Functor.Contravariant.Divisible hiding (divide)
import Data.Functor.Monoidal
import Data.Kind
import Data.Void
import Prelude hiding (id, (.))

--------------------------------------------------------------------------------

main :: IO ()
main = runCarExample

--------------------------------------------------------------------------------
-- Car Example from co-log blog post
-- https://kowainik.github.io/posts/2018-09-25-co-log#combinators

data Engine = Pistons Int | Rocket

data Car = Car
  { carMake :: String,
    carModel :: String,
    carEngine :: Engine
  }

engineToEither :: Engine -> Either Int ()
engineToEither e = case e of
  Pistons i -> Left i
  Rocket -> Right ()

carToTuple :: Car -> (String, (String, Engine))
carToTuple (Car make model engine) = (make, (model, engine))

carL :: LogAction IO Car
carL =
  carToTuple
    >$< (constL "Logging make..." *< showL >* constL "Finished logging make...")
      >*< (constL "Logging model.." *< showL >* constL "Finished logging model...")
      >*< ( engineToEither
              >$< constL "Logging pistons..."
              *< intL
              >|< constL "Logging rocket..."
          )

runCarExample :: IO ()
runCarExample = usingLoggerT carL $ logMsg $ Car "Toyota" "Corolla" (Pistons 4)

--------------------------------------------------------------------------------

newtype LogAction m msg = LogAction {unLogAction :: msg -> m ()}

instance Contravariant (LogAction m) where
  contramap :: (a -> b) -> LogAction m b -> LogAction m a
  contramap f (LogAction act) = LogAction $ \a -> act (f a)

instance Applicative m => Semigroupal (->) (,) (,) (LogAction m) where
  combine :: (LogAction m a, LogAction m b) -> LogAction m (a, b)
  combine (act1, act2) = LogAction $ \(a, b) ->
    unLogAction act1 a
      *> unLogAction act2 b
      *> pure ()

instance Applicative m => Unital (->) () () (LogAction m) where
  introduce :: () -> LogAction m ()
  introduce () = LogAction $ \_ -> pure ()

instance Applicative m => Semigroupal (->) Either (,) (LogAction m) where
  combine :: (LogAction m a, LogAction m b) -> LogAction m (Either a b)
  combine (act1, act2) = LogAction $ \case
    Left a -> coerce act1 a
    Right b -> coerce act2 b

instance Applicative m => Unital (->) Void () (LogAction m) where
  introduce :: () -> LogAction m Void
  introduce () = LogAction $ \_ -> pure ()

-- NOTE: We don't actually need these instances but include them to demonstrate the equivalence:
-- instance Applicative m => Semigroup (LogAction m a) where
--   act1 <> act2 = contramap (split @_ @(,)) $ combine (act1, act2)
--
-- instance Applicative m => Monoid (LogAction m a) where
--   mempty = contramap (\_ -> ()) $ introduce ()
--
-- instance Applicative m => Divisible (LogAction m) where
--   conquer :: LogAction m a
--   conquer = mempty
--
--   divide :: (a -> (b, c)) -> LogAction m b -> LogAction m c -> LogAction m a
--   divide f act1 act2 = contramap f $ combine (act1, act2)
--
-- instance Applicative m => Decidable (LogAction m) where
--     lose :: (a -> Void) -> LogAction m a
--     lose f = contramap f $ introduce @_ @Void ()
--
--     choose :: (a -> Either b c) -> LogAction m b -> LogAction m c -> LogAction m a
--     choose f act1 act2 = contramap f $ combine @_ @Either (act1, act2)

--------------------------------------------------------------------------------
-- Combinators

divide :: (Contravariant f, Semigroupal (->) (,) (,) f) => (a -> (b, c)) -> f b -> f c -> f a
divide f fb fc = curry (contramap f . combine) fb fc

infixr 3 >$<

(>$<) :: (a -> b) -> LogAction m b -> LogAction m a
(>$<) = contramap

infixr 4 >*<

(>*<) :: Semigroupal (->) (,) (,) f => f a -> f b -> f (a, b)
(>*<) = (|?|)

infixr 3 >|<

(>|<) :: Semigroupal (->) Either (,) f => f a -> f b -> f (Either a b)
(>|<) = (|?|)

infixr 4 >*

(>*) :: (Contravariant f, (Semigroupal (->) (,) (,) f)) => f a -> f () -> f a
(>*) = divide (,())

infixr 4 *<

(*<) :: (Contravariant f, (Semigroupal (->) (,) (,) f)) => f () -> f a -> f a
(*<) = divide ((),)

--------------------------------------------------------------------------------
-- Log Actions

hoistLogAction :: (forall x. m x -> n x) -> LogAction m a -> LogAction n a
hoistLogAction nat (LogAction act) = LogAction $ nat . act

liftLogAction :: (Monad m, MonadTrans t) => LogAction m msg -> LogAction (t m) msg
liftLogAction = hoistLogAction lift

logStringStdout :: LogAction IO String
logStringStdout = LogAction putStrLn

-- Combinator that allows to log any showable value
showL :: Show a => LogAction IO a
showL = contramap show logStringStdout

-- Returns a log action that logs a given string ignoring its input.
constL :: String -> LogAction IO a
constL s = s >$ logStringStdout

intL :: LogAction IO Int
intL = showL

--------------------------------------------------------------------------------

class HasLog env msg (m :: Type -> Type) where
  getLogAction :: env -> LogAction m msg
  setLogAction :: LogAction m msg -> env -> env

instance HasLog (LogAction m msg) msg m where
  getLogAction :: LogAction m msg -> LogAction m msg
  getLogAction = id

  setLogAction :: LogAction m msg -> LogAction m msg -> LogAction m msg
  setLogAction = const

logMsg :: (MonadReader env m, HasLog env msg m) => msg -> m ()
logMsg msg = do
  LogAction logger <- asks getLogAction
  logger msg

usingLoggerT :: Monad m => LogAction m msg -> LoggerT msg m a -> m a
usingLoggerT action = flip runReaderT (liftLogAction action) . runLoggerT

newtype LoggerT msg m a = LoggerT {runLoggerT :: ReaderT (LogAction (LoggerT msg m) msg) m a}
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadReader (LogAction (LoggerT msg m) msg))

instance MonadTrans (LoggerT msg) where
  lift :: Monad m => m a -> LoggerT msg m a
  lift = LoggerT . lift
