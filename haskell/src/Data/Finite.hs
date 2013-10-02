{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Constructively finite types.
module Data.Finite
    ( -- * Constructively finite types
      HasSize(..), Finite(..)
    , toFin, fromFin, finConv

      -- * Finiteness proofs
    , finite_Fin, finite_Either, finite_predMaybe
    , isoPresSize
    )
    where

import           Data.Iso
import           Control.Arrow ((***), (+++))
import           Control.Lens
import qualified Data.Void     as DV
import           Data.Type.Equality
import           Data.Fin
import           Data.Fin.Isos
import           Data.Type.Isos
import           Data.Type.Nat
import           Data.Proxy

import           Unsafe.Coerce (unsafeCoerce)

------------------------------------------------------------
--  Constructively finite types

class HasSize l where
  type Size l :: Nat
  -- ^ An type family giving the size of @l@.

  size        :: p l -> SNat (Size l)
  -- ^ Get the size of a finite type.

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
data Finite l where
  F :: (Eq l, HasSize l) => Fin (Size l) <-> l -> Finite l
  -- ^ Isomorphism witnessing the finiteness of @l@.

toFin       :: Finite l -> l -> Fin (Size l)
-- ^ One direction of the isomorphism as a function, provided for
--   convenience.
toFin (F finite) = view (from finite)

fromFin     :: Finite l -> Fin (Size l) -> l
-- ^ The other direction of the isomorphism as a function, provided
--   for convenience.
fromFin (F finite) = view finite

instance Natural n => HasSize (Fin n) where
  type Size (Fin n) = n
  size _ = toSNat

finite_Fin :: Natural n => Finite (Fin n)
finite_Fin = F id

instance HasSize DV.Void where
  type Size DV.Void = Z
  size _ = SZ

finite_Void :: Finite DV.Void
finite_Void = F $ iso absurd DV.absurd

instance HasSize () where
  type Size () = S Z
  size _ = SS SZ

finite_Unit :: Finite ()
finite_Unit = F $ iso (const ()) (const FZ)

instance HasSize a => HasSize (Maybe a) where
  type Size (Maybe a) = S (Size a)
  size _ = SS (size (Proxy :: Proxy a))

finite_Maybe :: Finite a -> Finite (Maybe a)
finite_Maybe a@(F{}) = F $ iso toM fromM
    where
      toM FZ         = Nothing
      toM (FS n)     = Just $ fromFin a n

      fromM Nothing  = FZ
      fromM (Just l) = FS (toFin a l)

finite_predMaybe :: forall a. (Eq a, HasSize a) => Finite (Maybe a) -> Finite a
finite_predMaybe (F isoM) =
  F $ subtractIso id (succFin . isoM . maybeEither)
  -- This is neat but it may not be the isomorphism one would
  -- "expect".  On the other hand, it is nice "memory-wise": instead
  -- of shifting everything after the Nothing to the left, it
  -- essentially takes the element that used to correspond to 0 and
  -- sticks it where the Nothing was, followed by re-indexing
  -- everything so index 0 is now where index 1 used to be.
  --
  -- XXX draw some pictures.

instance HasSize Bool where
  type Size (Bool) = S (S Z)
  size _ = SS (SS SZ)

finite_Bool :: Finite Bool
finite_Bool = F$ iso (\s -> case s of FZ -> False; FS FZ -> True)
                     (\b -> case b of False -> FZ; True -> FS FZ)

instance (HasSize a, HasSize b) => HasSize (Either a b) where
  type Size (Either a b) = Plus (Size a) (Size b)
  size _ = plus (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))

finite_Either :: forall a b. Finite a -> Finite b -> Finite (Either a b)
finite_Either a@(F{}) b@(F{}) =
    F $ iso ((fromFin a +++ fromFin b) . finSum' szA szB)
           (finSum szA szB . (toFin a +++ toFin b))
      where
        szA = size a
        szB = size b

instance (HasSize a, HasSize b) => HasSize (a,b) where
  type Size (a,b) = Times (Size a) (Size b)
  size _ = times (size (Proxy :: Proxy a)) (size (Proxy :: Proxy b))

finite_Product :: Finite a -> Finite b -> Finite (a,b)
finite_Product a@(F{}) b@(F{}) =
    F $ iso ((fromFin a *** fromFin b) . finProd' szA szB)
               (finProd szA szB . (toFin a *** toFin b))
      where
        szA = size a
        szB = size b


{- NOTE, it is actually not possible to make a reasonable implementation of

  finite_splitProduct :: Finite (a,b) -> (Finite a, Finite b)

because there is no guarantee that there is any sort of regularity in
the way the pairs are distributed.
-}

-- Finite is almost a BFunctor...
-- instance BFunctor Finite where
--   bmap i = iso (\(F f) -> F (f . i))
--                (\(F f) -> F (f . from i))

finConv :: (Eq l2, HasSize l2) => (l1 <-> l2) -> Finite l1 -> Finite l2
finConv i (F f) =
  case isoPresSize i of Refl -> F (f . i)

------------------------------------------------------------
-- Miscellaneous proofs about size

-- | We take as an axiom that isomorphisms preserve size
--   (unfortunately it is not actually possible to prove this within
--   Haskell).
isoPresSize :: forall l1 l2. (HasSize l1, HasSize l2) =>
               (l1 <-> l2) -> (Size l1 :=: Size l2)
isoPresSize _
  | snatEq s1 s2 = unsafeCoerce Refl
  | otherwise = error $ "isoPresSize: " ++ show s1 ++ " /= " ++ show s2
  where s1 = size (Proxy :: Proxy l1)
        s2 = size (Proxy :: Proxy l2)
