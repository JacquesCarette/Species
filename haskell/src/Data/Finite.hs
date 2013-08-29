{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Natural transformations, isomorphisms, and constructively finite types.
module Data.Finite
    ( -- * Isomorphisms and natural transformations

     type (<->), liftIso, isoPresSize, type (-->), type (<-->)

      -- * Constructively finite types
    , Finite(..)
    )
    where

import           Control.Arrow ((***), (+++))
import           Control.Lens
import qualified Data.Void     as DV
import           Data.Type.Equality
import           Data.Fin
import           Data.Fin.Isos
import           Data.Type.Nat
import           Data.Proxy

import           Unsafe.Coerce (unsafeCoerce)

------------------------------------------------------------
--  Isomorphisms

-- | The type @a \<-\> b@ represents isomorphisms between @a@ and @b@.
--
--   * To construct one, you can pass a pair of inverse functions to
--     'iso', or use 'liftIso' as described below.
--
--   * To invert an isomorphism, use @'from' :: (a \<-\> b) -> (b \<-\> a)@.
--
--   * To compose two isomorphisms, use the normal function
--     composition operator '.' (though note it works \"backwards\",
--     /i.e./ @(.) :: (a \<-\> b) -> (b \<-\> c) -> (a \<-\> c)@.
--
--   * To turn an isomorphism into a function, use @'view' :: (a \<-\>
--     b) -> (a -> b)@.
type (<->) a b = Iso' a b

-- | Higher-order isomorphisms, /i.e./ natural isomorphisms, between
--   two shapes.
type (<-->) f g = forall l. (Eq l, Finite l) => f l <-> g l

-- | Lift an isomorphism on a particular field to an isomorphism of an
--   entire structure.  Unfortunately, the field must be passed twice
--   (this is simply due to a quirk of the way @lens@ is encoded).  For example,
--
--   > liftIso _1 _1 :: (a <-> b) -> ((a,c) <-> (b,c))
liftIso :: Setter s t a b -> Setter t s b a -> (a <-> b) -> (s <-> t)
liftIso l1 l2 ab = withIso ab $ \f g -> iso (l1 %~ f) (l2 %~ g)

------------------------------------------------------------
--  Natural transformations

-- | Natural transformations between two shapes.
type (-->) f g = forall l. (Eq l, Finite l) => f l -> g l

------------------------------------------------------------
--  Constructively finite types

-- | Constructively finite types.
--
--   Currently, a finite type is defined as a type @l@ for which there
--   exists an isomorphism between @l@ and @Fin n@ for some natural
--   number @n@.  However, this is a bit stronger than we would like:
--   we can use the isomorphism to induce orderings on the inhabitants
--   of @l@ from orderings of @Fin n@ (which are easy to compute).
--   Abstractly, however, the notions of finiteness and linear
--   orderings ought to be orthogonal.  We must be careful to note
--   when we are taking advantage of this implicit ordering.
class Eq l => Finite l where

  type Size l :: Nat
  -- ^ An associated type family giving the size of @l@.

  size        :: Proxy l -> SNat (Size l)
  -- ^ Get the size of a finite type.

  finite      :: Fin (Size l) <-> l
  -- ^ Isomorphism witnessing the finiteness of @l@.

  toFin       :: l -> Fin (Size l)
  -- ^ One direction of the isomorphism as a function, provided for
  --   convenience.
  toFin = view (from finite)

  fromFin     :: Fin (Size l) -> l
  -- ^ The other direction of the isomorphism as a function, provided
  --   for convenience.
  fromFin = view finite

instance Natural n => Finite (Fin n) where
  type Size (Fin n) = n
  size _ = toSNat
  finite = id

instance Finite DV.Void where
  type Size DV.Void = Z
  size _ = SZ
  finite = iso absurd DV.absurd

instance Finite () where
  type Size () = S Z
  size _ = SS SZ
  finite = iso (const ()) (const FZ)

instance Finite a => Finite (Maybe a) where
  type Size (Maybe a) = S (Size a)
  size _ = SS (size (Proxy :: Proxy a))
  finite = iso toM fromM
    where
      toM :: Fin (S (Size a)) -> Maybe a
      toM FZ         = Nothing
      toM (FS n)     = Just $ fromFin n

      fromM :: Maybe a -> Fin (S (Size a))
      fromM Nothing  = FZ
      fromM (Just l) = FS (toFin l)

instance Finite Bool where
  type Size (Bool) = S (S Z)
  size _ = SS (SS SZ)
  finite = iso (\s -> case s of FZ -> False; FS FZ -> True)
               (\b -> case b of False -> FZ; True -> FS FZ)

instance (Finite a, Finite b) => Finite (Either a b) where
  type Size (Either a b) = Plus (Size a) (Size b)
  size _ = plus (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))
  finite = iso ((fromFin +++ fromFin) . finSum' szA szB)
               (finSum szA szB . (toFin +++ toFin))
    where
      szA = size (Proxy :: Proxy a)
      szB = size (Proxy :: Proxy b)

instance (Finite a, Finite b) => Finite (a,b) where
  type Size (a,b) = Times (Size a) (Size b)
  size _ = times (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))
  finite = iso ((fromFin *** fromFin) . finProd' szA szB)
               (finProd szA szB . (toFin *** toFin))
    where
      szA = size (Proxy :: Proxy a)
      szB = size (Proxy :: Proxy b)

------------------------------------------------------------
-- Miscellaneous proofs about size

-- | We take as an axiom that isomorphisms preserve size
--   (unfortunately it is not actually possible to prove this within
--   Haskell).
isoPresSize :: forall l1 l2. (Finite l1, Finite l2) =>
               (l1 <-> l2) -> (Size l1 :=: Size l2)
isoPresSize _
  | snatEq s1 s2 = unsafeCoerce Refl
  | otherwise = error $ "isoPresSize: " ++ show s1 ++ " /= " ++ show s2
  where s1 = size (Proxy :: Proxy l1)
        s2 = size (Proxy :: Proxy l2)
