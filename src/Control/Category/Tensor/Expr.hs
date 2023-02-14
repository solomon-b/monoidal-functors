{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Control.Category.Tensor.Expr
  ( -- * Type Families
    MConcat,
    Tensored (..),
    type (++),

    -- * AppendTensored
    AppendTensored (..),
  )
where

import Control.Category.Tensor
import Data.Function
import Data.Kind
import Prelude (Eq, Ord, Show)

--------------------------------------------------------------------------------

-- |
--
-- __Examples:__
--
-- >>> :{
--  let foo :: Tensored (,) () '[Bool, Int]
--      foo = Tensored (True, (8, ()))
-- :}
--
-- >>> :{
-- let bar :: Tensored Either Void '[Bool, Int]
--     bar = Tensored $ Right $ Left 8
-- :}
--
-- >>> :{
-- let baz :: Tensored These Void '[Bool, Int]
--     baz = Tensored $ These True $ This 8
-- :}
type MConcat :: (Type -> Type -> Type) -> Type -> [Type] -> Type
type family MConcat mappend mempty xs where
  MConcat mappend mempty '[] = mempty
  MConcat mappend mempty (x ': xs) = mappend x (MConcat mappend mempty xs)

newtype Tensored t i xs = Tensored {getTensored :: MConcat t i xs}

deriving newtype instance Show (MConcat t i xs) => Show (Tensored t i xs)

deriving newtype instance Eq (MConcat t i xs) => Eq (Tensored t i xs)

deriving newtype instance Ord (MConcat t i xs) => Ord (Tensored t i xs)

--------------------------------------------------------------------------------

type (++) :: [k] -> [k] -> [k]
type family xs ++ ys where
  '[] ++ xs = xs
  (x ': xs) ++ ys = x ': (xs ++ ys)

class AppendTensored xs where
  appendTensored :: Tensor (->) t i => Tensored t i xs `t` Tensored t i ys -> Tensored t i (xs ++ ys)

instance AppendTensored '[] where
  appendTensored = fwd unitl . glmap getTensored

instance AppendTensored xs => AppendTensored (x ': xs) where
  appendTensored = Tensored . grmap (getTensored . appendTensored @xs . glmap Tensored) . bwd assoc . glmap getTensored
