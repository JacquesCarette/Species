{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}

-- | Convert back and forth between containers and labelled structures.
module Data.Species.Convert where

import           Data.Functor            ((<$>))
import           Data.Functor.Compose
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Coproduct

import           Data.Void

import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Storage

import           Data.Species.List

------------------------------------------------------------
-- Converting between containers and labelled structures
------------------------------------------------------------

-- There are two kinds of containers:
-- 1. Those which are fully polymorphic in their labels, in other words
--    the labels are implicit, corresponding to Sp' structures
-- 2. Those where the labels form an integral part of the container

-- For the Implicitly labelled structures:
class ImpLabelled c where
  type EltType c :: *
  type ShapeOf c :: * -> *
  toLabelled   :: Storage s => c -> Sp' (ShapeOf c) s (EltType c)
  elimLabelled :: Elim (ShapeOf c) (EltType c) c
  fromLabelled :: (Eq l, Storage s) => Sp (ShapeOf c) s l (EltType c) -> c
  fromLabelled = elim elimLabelled
  fromLabelled' :: Sp' (ShapeOf c) s (EltType c) -> c
  fromLabelled' = elim' elimLabelled

instance ImpLabelled (Identity a) where
  type EltType (Identity a) = a
  type ShapeOf (Identity a) = X
  elimLabelled = elimX Identity
  toLabelled   = x' . runIdentity

instance ImpLabelled Void where
  type EltType Void = Void
  type ShapeOf Void = Zero
  elimLabelled = elimZero
  toLabelled _ = undefined

instance ImpLabelled () where
  type EltType () = ()
  type ShapeOf () = One
  elimLabelled = elimOne ()
  toLabelled () = one'

instance ( ImpLabelled (f a), ImpLabelled (g a)
         , EltType (f a) ~ a, EltType (g a) ~ a
         )
    => ImpLabelled (Product f g a) where
  type EltType (Product f g a) = a
  type ShapeOf (Product f g a) = ShapeOf (f a) * ShapeOf (g a)
  elimLabelled = elimProd $ elimLabelled <#> \fa -> elimLabelled <#> \ga -> Pair fa ga
  toLabelled (Pair a b) = prod' (toLabelled a) (toLabelled b)

infixr 4 <#>
(<#>) :: Functor f => f a -> (a -> b) -> f b
(<#>) = flip fmap

instance ( ImpLabelled (f a), ImpLabelled (g a)
         , EltType (f a) ~ a, EltType (g a) ~ a
         )
    => ImpLabelled (Coproduct f g a) where
  type EltType (Coproduct f g a) = a
  type ShapeOf (Coproduct f g a) = (ShapeOf (f a)) + (ShapeOf (g a))
  elimLabelled = elimSum (elimLabelled <#> left)
                         (elimLabelled <#> right)
  toLabelled (Coproduct (Left a)) = inl' $ toLabelled a
  toLabelled (Coproduct (Right a)) = inr' $ toLabelled a

{-
instance ( Functor f
         , ImpLabelled (g a)
         , ImpLabelled (f (g a))
         , EltType (f (g a)) ~ g a
         , EltType    (g a)  ~   a

           {- we really want a constraint like

                forall x y. ShapeOf (f x) ~ ShapeOf (f y)

              but Haskell doesn't currently support such
              universally quantified constraints, so we
              have to make do with enumerating the
              necessary instantiations.
           -}
         , ShapeOf (f (g a)) ~ ShapeOf (f (Sp' (ShapeOf (g a)) s a))

         )
    => ImpLabelled (Compose f g a) where
  type EltType (Compose f g a) = a
  type ShapeOf (Compose f g a)
    = Comp (ShapeOf (f (Sp' (ShapeOf (g a)) s (EltType (g a)))))
           (ShapeOf (g a))
  toLabelled (Compose fga)
    = compJ'' (fmap toLabelled (toLabelled fga))
  elimLabelled
    = elimComp (Compose <$> elimLabelled) elimLabelled
-}

instance ImpLabelled [a] where
  type EltType [a] = a
  type ShapeOf [a] = L
  elimLabelled     = elimList [] (:)
  toLabelled       = fromList
