{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | A collection of examples of Species

module Data.Species.Examples where

import           Control.Lens       (Iso, from, iso, view)
import           Data.Functor       ((<$>))
import qualified Data.MultiSet    as MS

import           Data.BFunctor
import           Data.Iso (liftIso,type (<->))
import           Data.Species.Convert
import           Data.Species.Elim
import           Data.Species.List
import           Data.Species.Shape
import           Data.Species.Types
import           Data.Storage
import           Data.Finite
import           Data.Fin
import           Data.Hashable
import           Data.Type.Nat (Natural,Nat(..),SNat(..),natty)
import           Data.Fin.Isos
import qualified Data.Set.Abstract as S
import qualified Data.HashMap.Lazy as HM
import qualified Data.Map          as Map
import           Data.HashMap.Lazy ((!))
import qualified Data.Vec          as Vec
import qualified Data.Species.List as L

------------------------------------------------------------------------------

-- | Haskell MultiSet is an unlabelled Bag
--   Note in particular how in the eliminator call we ignore the label.
fromMS :: Storage s => MS.MultiSet a -> Sp' E s a
fromMS = e' . MS.elems

instance ImpLabelled (MS.MultiSet a) where
  type EltType (MS.MultiSet a) = a
  type ShapeOf (MS.MultiSet a) = E
  elimLabelled          = elimE (S.smap snd)
  toLabelled            = fromMS

toMS :: (Eq l, Storage s) => Sp E s l a -> MS.MultiSet a
toMS = fromLabelled

toMS' :: (Storage s) => Sp' E s a -> MS.MultiSet a
toMS' = fromLabelled'

------------------------------------------------------------------------------

-- | Much like Rose trees, rooted (multi-arity) trees use a set rather than 
--   a list of sub-trees.  Since terminology between combinatorics and PL
--   conflicts, we'll stick with 'Arbo' (from the French arborescence) instead
--   of trying to invent some tree variant (as it would be misunderstood 
--   almost surely anyways).
newtype Arbo l = Arbo {unArbo :: (X * (Comp E Arbo)) l }

-- | fold and unfold.  This is so systematic, it should be automated.
isoArbo :: Iso (Arbo l) (Arbo l') ((X*(Comp E Arbo)) l) ((X*(Comp E Arbo)) l')
isoArbo = iso unArbo Arbo

instance BFunctor Arbo where
  bmap g = liftIso isoArbo isoArbo (bmap g)

-- | Introduce a general tree shape.
arbo_ :: (X*(Comp E Arbo)) l -> Arbo l
arbo_ = view (from isoArbo)

-- | Introduce a general tree structure.
arbo :: Eq l => Sp (X*(Comp E Arbo)) s l a -> Sp Arbo s l a
arbo = reshape (view (from isoArbo))

-- | And its existantially quantified form
arbo' :: Sp' (X*(Comp E Arbo)) s a -> Sp' Arbo s a
arbo' sp' = case sp' of SpEx sp -> SpEx (arbo sp)

node :: Storage s => a -> Sp' E s (Sp' Arbo s a) -> Sp' Arbo s a
node a ts = arbo' $ prod' (x' a) (compJ'' ts)

-- | An eliminator for labelled general tree structures, the equivalent of
--   'foldr'.  Explicitly polymorphic on the labels.
elimArbo :: (forall l1. a -> S.Set (l1, r) -> r) -> Elim Arbo l a r
elimArbo f =
  mapElimShape (view isoArbo) $
    elimProd (const $ elimX (\a -> elimComp (elimE (f a)) (elimArbo f)))

data SetTree a = SetTree a (MS.MultiSet (SetTree a))

fromSetTree :: Storage s => SetTree a -> Sp' Arbo s a
fromSetTree (SetTree a st) = node a (fromMS (MS.mapMonotonic fromSetTree st))

instance ImpLabelled (SetTree a) where
  type EltType (SetTree a) = a
  type ShapeOf (SetTree a) = Arbo
  elimLabelled             = elimArbo (\a ms -> SetTree a (S.smap snd ms))
  toLabelled               = fromSetTree

------------------------------------------------------------------------------
-- | Haskell HashMap is (essentially) a labelled bag (with Hashable labels)
--   To make things work though, we really need to package up a Finite l
--   in our data-structure, and ask for it when needed.  We also package up
--   the needed Hashable.
data FinHashMap l v where
   FHM :: (Hashable l, Eq l) => Finite l -> HM.HashMap l v -> FinHashMap l v

fromFHM :: (Storage s) => FinHashMap l a -> Sp E s l a
fromFHM (FHM fin hm) = e fin (\l -> hm ! l)

toFHM :: (Eq l, Hashable l, Storage s) => Finite l -> Sp E s l a -> FinHashMap l a
toFHM finl s = elim (elimExpLabelled finl) s

-- Note the use of MS.fold here; we could instead implement a fold on our
-- abstract sets, but that feels like we would be revealing too much
-- information.  Of course, what we have here is not really better!  It
-- is entirely correct though.  This really needs to be done in Agda...
instance (Hashable l, Eq l) => ExpLabelled (FinHashMap l a) where
  type EltLT     (FinHashMap l a) = a
  type ShapeOfLT (FinHashMap l a) = E
  type LabelType (FinHashMap l a) = l
  toExpLabelled                   = fromFHM
  elimExpLabelled pf              = elimE f 
    where f s = FHM pf (MS.fold (\(l,x) hm -> HM.insert l x hm) HM.empty (S.smap id s))

------------------------------------------------------------------------------
-- | Haskell's FiniteMap is also (essentially) a labelled bag, but this time
--   the constraint is that labels be Ord(erable).
--   And again, the FiniteMap data-structure is too 'raw' on its own, we
--   need to package up Finite and Ord.
--   It is also worthwhile to see that the code below is essentially identical
--   to the code for FinHashMap.  The only true difference is the constraint,
--   aka the amount of structure we have on labels.
data FinMap l v where
   FM :: (Ord l, Eq l) => Finite l -> Map.Map l v -> FinMap l v

fromFM :: (Storage s) => FinMap l a -> Sp E s l a
fromFM (FM fin m) = e fin ((Map.!) m)

toFM :: (Ord l, Eq l, Storage s) => Finite l -> Sp E s l a -> FinMap l a
toFM finl s = elim (elimExpLabelled finl) s

instance (Ord l, Eq l) => ExpLabelled (FinMap l a) where
  type EltLT     (FinMap l a) = a
  type ShapeOfLT (FinMap l a) = E
  type LabelType (FinMap l a) = l
  toExpLabelled               = fromFM
  elimExpLabelled pf          = elimE f 
    where f s = FM pf (MS.fold (\(l,x) hm -> Map.insert l x hm) Map.empty (S.smap id s))

------------------------------------------------------------------------------
-- | Length-indexed vectors are more interesting.

-- | Convert a Haskell length-indexed vector to a list structure with 
--   explicit Fin labels.
fromVec :: forall a n s. Storage s => Vec.Vec n a -> Sp L s (Fin n) a
fromVec Vec.VNil = nil
fromVec (Vec.VCons a v) = 
    let m = Vec.size v in
    natty m $ relabel (finSumI (SS SZ) m) $ cons a (fromVec v)

{- the code below is 'morally right', but Haskell can't see it.
   Basically, it (rightly) can't see that l2 ~ Fin k.  
elimVec :: forall a n. SNat n -> Elim L (Fin n) a (Vec.Vec n a)
elimVec n = mapElimShape (view isoL) $ elimSum' n
    where
      elimSum' :: SNat n -> Elim (One + X*L) (Fin n) a (Vec.Vec n a)
      elimSum' SZ = Elim $ \(Inl (One _)) _ -> Vec.VNil
      elimSum' (SS k) = elimSum (undefined) 
          (elimProd $ const (elimX $ \a -> fmap (Vec.VCons a) (elimVec k)))
-}

-- This Natural constraint should be possible to remove, later.
instance Natural n => ExpLabelled (Vec.Vec n a) where
  type EltLT     (Vec.Vec n a) = a
  type ShapeOfLT (Vec.Vec n a) = L
  type LabelType (Vec.Vec n a) = Fin n
  toExpLabelled                = fromVec
  elimExpLabelled pf           = undefined -- elimVec (size pf)
