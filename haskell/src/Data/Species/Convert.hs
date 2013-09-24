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

-- import           Data.Finite
import           Data.Species.Elim
import           Data.Species.Shape
import           Data.Species.Types

import           Data.Species.List

------------------------------------------------------------
-- Converting between containers and labelled structures
------------------------------------------------------------

class Labelled c where
  type EltType c :: *
  type ShapeOf c :: * -> *
  toLabelled   :: c -> Sp' (ShapeOf c) (EltType c)
  elimLabelled :: Elim (ShapeOf c) (EltType c) c
  fromLabelled :: Eq l => Sp (ShapeOf c) l (EltType c) -> c
  fromLabelled = elim elimLabelled
  fromLabelled' :: Sp' (ShapeOf c) (EltType c) -> c
  fromLabelled' = elim' elimLabelled

instance Labelled (Identity a) where
  type EltType (Identity a) = a
  type ShapeOf (Identity a) = X
  toLabelled   = x' . runIdentity
  elimLabelled = elimX Identity

instance Labelled Void where
  type EltType Void = Void
  type ShapeOf Void = Zero
  toLabelled _ = undefined
  elimLabelled = elimZero

instance Labelled () where
  type EltType () = ()
  type ShapeOf () = One
  toLabelled () = one'
  elimLabelled = elimOne ()

instance ( Labelled (f a), Labelled (g a)
         , EltType (f a) ~ a, EltType (g a) ~ a
         )
    => Labelled (Product f g a) where
  type EltType (Product f g a) = a
  type ShapeOf (Product f g a) = ShapeOf (f a) * ShapeOf (g a)
  toLabelled (Pair a b) = prod' (toLabelled a) (toLabelled b)
  elimLabelled = elimProd $ elimLabelled <#> \fa -> elimLabelled <#> \ga -> Pair fa ga

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
  elimLabelled = elimSum (elimLabelled <#> left)
                         (elimLabelled <#> right)

instance ( Functor f
         , Labelled (g a)
         , Labelled (f (g a))
         , EltType (f (g a)) ~ g a
         , EltType    (g a)  ~   a

           {- we really want a constraint like

                forall x y. ShapeOf (f x) ~ ShapeOf (f y)

              but Haskell doesn't currently support such
              universally quantified constraints, so we
              have to make do with enumerating the
              necessary instantiations.
           -}
         , ShapeOf (f (g a)) ~ ShapeOf (f (Sp' (ShapeOf (g a)) a))

         )
    => Labelled (Compose f g a) where
  type EltType (Compose f g a) = a
  type ShapeOf (Compose f g a)
    = Comp (ShapeOf (f (Sp' (ShapeOf (g a)) (EltType (g a)))))
           (ShapeOf (g a))
  toLabelled (Compose fga)
    = compJ'' (fmap toLabelled (toLabelled fga))
  elimLabelled
    = elimComp (Compose <$> elimLabelled) elimLabelled

instance Labelled [a] where
  type EltType [a] = a
  type ShapeOf [a] = L
  toLabelled       = fromList
  elimLabelled     = elimList [] (:)
