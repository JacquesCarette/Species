{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}

-- | Convert back and forth between containers and labelled structures.
module Data.Species.Convert where

import           Data.Functor
import           Data.Functor.Compose
import           Data.Functor.Constant
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Coproduct

import           Data.Void

import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Types

------------------------------------------------------------
-- Converting between containers and labelled structures
------------------------------------------------------------

class Labelled c where
  type EltType c :: *
  type ShapeOf c :: * -> *
  toLabelled   :: c -> Sp' (ShapeOf c) (EltType c)
  fromLabelled :: Elim (ShapeOf c) (EltType c) c

instance Labelled (Identity a) where
  type EltType (Identity a) = a
  type ShapeOf (Identity a) = X
  toLabelled   = x' . runIdentity
  fromLabelled = elimX Identity

instance Labelled Void where
  type EltType Void = Void
  type ShapeOf Void = Zero
  toLabelled _ = undefined
  fromLabelled = elimZero

instance Labelled () where
  type EltType () = ()
  type ShapeOf () = One
  toLabelled () = one'
  fromLabelled = elimOne ()

instance ( Labelled (f a), Labelled (g a)
         , EltType (f a) ~ a, EltType (g a) ~ a
         )
    => Labelled (Product f g a) where
  type EltType (Product f g a) = a
  type ShapeOf (Product f g a) = ShapeOf (f a) * ShapeOf (g a)
  toLabelled (Pair a b) = prod' (toLabelled a) (toLabelled b)
  fromLabelled = elimProd $ fromLabelled <#> \fa -> fromLabelled <#> \ga -> Pair fa ga

infixr 4 <#>
(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip fmap

instance ( Labelled (f a), Labelled (g a)
         , EltType (f a) ~ a, EltType (g a) ~ a
         )
    => Labelled (Coproduct f g a) where
  type EltType (Coproduct f g a) = a
  type ShapeOf (Coproduct f g a) = (ShapeOf (f a)) + (ShapeOf (g a))
  toLabelled (Coproduct (Left a)) = inl' $ toLabelled a
  toLabelled (Coproduct (Right a)) = inr' $ toLabelled a
  fromLabelled = elimSum (fromLabelled <#> left)
                         (fromLabelled <#> right)


-- XXX ugh, these constraints can't be right
instance ( Functor f, Labelled (g a)
         , Labelled (f (Sp' (ShapeOf (g a)) (EltType (g a))))
         , EltType (f (Sp' (ShapeOf (g a)) (EltType (g a))))
           ~ Sp' (ShapeOf (g a)) a
         )
    => Labelled (Compose f g a) where
  type EltType (Compose f g a) = a
  type ShapeOf (Compose f g a)
    = Comp (ShapeOf (f (Sp' (ShapeOf (g a)) (EltType (g a)))))
           (ShapeOf (g a))
  toLabelled (Compose fga)
    = case toLabelled (fmap toLabelled fga) of
        SpEx sp -> compJ' sp
  -- fromLabelled :: Elim (Comp ...) a (Compose f g a)
  fromLabelled
    = elimComp undefined undefined -- XXX still working on this one
