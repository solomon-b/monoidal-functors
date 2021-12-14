{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
module Control.Category.Tensor.Expr where

import Control.Category.Tensor
import Data.Function
import Data.Kind

type Tensored
  :: (Type -> Type -> Type)
  -> Type
  -> [Type]
  -> Type
data Tensored t i vs
  where
  ANil :: i -> Tensored t i '[]
  ACons :: t v (Tensored t i vs) -> Tensored t i (v ': vs)

{-
Examples:
foo :: Tensored (,) () '[Bool, Int]
foo = bwd asNested (True, (8, ()))

bar :: Tensored Either Void '[Bool, Int]
bar = bwd asNested $ Right $ Left 8

baz :: Tensored These Void '[Bool, Int]
baz = bwd asNested $ These True $ This 8
-}

type AsNested :: (Type -> Type -> Type) -> Type -> [Type] -> Type -> Constraint
class Tensor t i (->) => AsNested t i xs unwrapped | t i xs -> unwrapped
  where
  asNested :: Tensor t i (->) => Iso (->) (Tensored t i xs) unwrapped

instance Tensor t i (->) => AsNested t i '[] i
  where
  asNested :: Tensor t i (->) => Iso (->) (Tensored t i '[]) i
  asNested = Iso to from
    where
      to :: Tensor t i (->) => Tensored t i '[] -> i
      to = \case
        ANil i -> i
      from :: Tensor t i (->) => i -> Tensored t i '[]
      from = ANil 
  
instance (Tensor t i (->), AsNested t i xs r) => AsNested t i (x ': xs) (x `t` r)
  where
  asNested :: Tensor t i (->) => Iso (->) (Tensored t i (x ': xs)) (x `t` r)
  asNested = Iso to from
    where
      to :: (AsNested t i xs r, Tensor t i (->)) => Tensored t i (x ': xs) -> (x `t` r)
      to = \case
        ACons xxs -> grmap (fwd asNested) xxs
      from :: (AsNested t i xs r, Tensor t i (->)) => (x `t` r) -> Tensored t i (x ': xs)
      from xtr = ACons $ grmap (bwd asNested) xtr

type (++) :: [k] -> [k] -> [k]
type family xs ++ ys
  where
  '[] ++ xs = xs
  (x ': xs) ++ ys = x ': (xs ++ ys)

class AppendTensored xs
  where
  appendTensored
    :: Tensor t i (->)
    => Tensored t i xs `t` Tensored t i ys
    -> Tensored t i (xs ++ ys)

instance AppendTensored '[]
  where
  appendTensored = fwd lunit . glmap (\case { ANil i -> i })

instance AppendTensored xs => AppendTensored (x ': xs)
  where
  appendTensored = ACons . grmap appendTensored . bwd assoc . glmap (\case { ACons i -> i })
