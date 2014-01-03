{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

------------------------------------------
-- The point of this module is to show that many vector operations
-- can be defined generally on species

module Data.Species.VecLike where

import           Prelude hiding (filter)
import           Control.Lens (iso,view,from)
import           Data.Type.Equality
import qualified Data.MultiSet            as MS

import           Data.BFunctor
import qualified Data.Fin                 as F
import           Data.Fin.Isos (finSum, finSum')
import           Data.Iso
import           Data.Finite
import           Data.Species.Shape
import           Data.Species.Shuffle
import           Data.Species.Types
import qualified Data.Type.Nat            as N
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus
import qualified Data.Storage             as S
import qualified Data.Set.Abstract        as Set
import qualified Data.Species.List        as L
import qualified Data.Vec                 as Vec
import           Data.Species.Examples
import           Data.Species.Elim

-- This requires quite a lot of inputs to 'work', but it does.
-- Given a species, its allocated size, the size of prefix you want to take,
-- a proof that it is smaller, overlay this with the Species.  Note that
-- this requires that the label set be F.Fin.  One could likely generalize
-- this to l <-> F.Fin q by explicitly adding such a parameter.
take :: forall f a q n s. 
  Sp f s (F.Fin q) a -> N.SNat q -> N.SNat n -> (n <= q) 
     -> Sp (f # Part) s (F.Fin q) a
take (Struct f i) qq n pf =
  case minus qq n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprod_ f (part_ sn sm isom)) i
          where isom :: Either (F.Fin n) (F.Fin m) <-> F.Fin q
                isom = iso (finSum n m) (finSum' n m)
                sn = N.natty n $ Set.enumerate finite_Fin
                sm = N.natty m $ Set.enumerate finite_Fin

-- As alluded to above, given a Finite l, we can actually "take" from
-- an arbitrary Species!  This shows the inherent danger of explicit
-- finiteness proofs for label sets: they contain quite a bit more information
-- then just 'finiteness'.
take' :: forall a f l n s. 
  Sp f s l a -> N.SNat (Size l) -> N.SNat n -> (n <= Size l) -> Finite l
     -> Sp (f # Part) s l a
take' (Struct f i) sizl n pf (F finl) =
  case minus sizl n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprod_ f (part_ sn sm (isom . finl))) i
          where isom :: Either (F.Fin n) (F.Fin m) <-> F.Fin (N.Plus n m)
                isom = iso (finSum n m) (finSum' n m)
                sn = N.natty n $ Set.enumerate finite_Fin
                sm = N.natty m $ Set.enumerate finite_Fin

-- Define a general 'partition' function, from which filter and remove
-- can easily be defined.
-- We can do this with an Enumerable constraint, which is less `leaky'
-- than a Finite proof.
partition :: (S.Storage s, Set.Enumerable l, Eq l) => 
          Sp f s l a -> (a -> Bool) -> Sp (f # Part) s l a
partition (Struct f stor) p = Struct (cprod_ f k) stor
  where sel = S.smap p stor -- force this?
        k = part_ Set.enumS Set.enumS
                  (iso (\l -> case l of {Left a -> a; Right a -> a}) 
                       (\l -> if (S.index sel l) then Left l else Right l) )

-- One question still nags: is the above really partition?  In other words,
-- could we implement (for example) Prelude.filter with the above?
-- First, let's implement the 'back half' first: given a species of 
-- shape L#Part, extract a filtered list of the 'left' part of the partition
extractLeft :: (S.LabelledStorage s, Set.Enumerable l, Eq l) => 
    Sp (L.L # Part) s l a -> [a]
extractLeft sp = 
  -- because of existentials, it is very hard to rewrite the code below
  -- in a less `inline' style.
  let (lsp, part) = decompL sp
  in gelim (L.gelimList [] 
      (\(l,a) r -> 
        case part of 
          Prod _ _ eiso ->
            case view (from eiso) l of
              Left _  -> a : r
              Right _ ->     r  )) lsp

-- for ease of use below, create specialized versions which work on 
-- an L-shape, using Fin labels, and (->) for storage.  Use LFA as an
-- abbreviation for these 3 aspects.
extractLFA :: N.Natural n => Sp (L.L # Part) (->) (F.Fin n) a -> [a]
extractLFA = extractLeft

partitionLFA :: N.Natural n => Sp L.L (->) (F.Fin n) a -> (a -> Bool) -> Sp (L.L # Part) (->) (F.Fin n) a
partitionLFA = partition

-- Victory!
filter' :: forall a. (a -> Bool) -> [a] -> [a]
filter' p lst = case Vec.fromList lst of
  Vec.SomeVec v -> 
      N.natty (Vec.size v) $ extractLFA $ partitionLFA (fromVec v) p

extractBoth :: (S.LabelledStorage s, Set.Enumerable l, Eq l) => 
    Sp (L.L # Part) s l a -> ([a], [a])
extractBoth sp = 
  -- because of existentials, it is very hard to rewrite the code below
  -- in a less `inline' style.
  let (lsp, part) = decompL sp
  in gelim (L.gelimList ([],[])
      (\(l,a) (ll,rl) -> 
        case part of 
          Prod _ _ eiso ->
            case view (from eiso) l of
              Left _  -> (a:ll,rl)
              Right _ -> (ll,a:rl))) lsp

extractBothLFA :: N.Natural n => Sp (L.L # Part) (->) (F.Fin n) a -> ([a],[a])
extractBothLFA = extractBoth

partition' :: (a -> Bool) -> [a] -> ([a],[a])
partition' p lst = case Vec.fromList lst of
  Vec.SomeVec v -> 
      N.natty (Vec.size v) $ extractBothLFA $ partitionLFA (fromVec v) p

-- We can just as easily implement, for all Species:
-- 1. elem
-- 2. find
-- 3. findIndex (returns Maybe l)
-- 4. elemIndex (returns Maybe l)
--
-- More interestingly, we can do findIndices too, by again re-using
-- Partition.  Since that is not entirely obvious, here is the 
-- complete implementation:
findIndices :: (S.Storage s, Set.Enumerable l, Eq l) => 
          Sp f s l a -> (a -> Bool) -> E l
findIndices sp p = elim k (Struct gl es)
  where sp' = partition sp p
        Struct (CProd _ gl) es = sp'
        k = elimProd $ \pf -> elimE $ \s -> elimE $ const
               (E $ Set.injectionMap (\(l,_) -> view pf (Left l)) s)

----------------------------------------------------------------
-- Like vectors, we can append labelled structures: this is exactly 
-- what species product gives.
sappend :: (S.Storage s, Eq l1, Eq l2) => Sp f s l1 a -> Sp g s l2 a -> Sp (f * g) s (Either l1 l2) a
sappend = prod

lappend :: (Eq l1, Eq l2) => Sp L.L (->) l1 a -> Sp L.L (->) l2 a -> Sp (L.L * L.L) (->) (Either l1 l2) a
lappend = sappend

-- we can concatenate two lists this way.  (This would be cleaner with
-- vectors...
lcat :: [a] -> [a] -> [a]
lcat l1 l2 = case (Vec.fromList l1, Vec.fromList l2) of
  (Vec.SomeVec v1, Vec.SomeVec v2) -> 
      N.natty (Vec.size v1) $ N.natty (Vec.size v2) $
           elim (elimProd 
               $ const (L.elimList L.toListElim (\_ _ -> L.toListElim)))
               $ lappend (fromVec v1) (fromVec v2)

-- TODO: once the Vector implementation is done, do that too.


----------------------------------------------------------------
-- Eliminators are, of course, folds.  So let's give an example.
-- Again we use partition to get the fundamental information, and then
-- extract it from there.
all :: (S.Storage s, Set.Enumerable l, Eq l) => Sp f s l a -> (a -> Bool) -> Bool
all sp p = elim k (Struct gl es)
  where sp' = partition sp p
        Struct (CProd _ gl) es = sp'
        k = elimProd (const $ elimE (const $ elimE Set.isEmpty))

-- With a=Bool, we can implement 'and' and 'or';
-- with a=Int, sum and product, etc.  This is basically because all of
-- those are associative-commutative operations, and so we can simply
-- *forget* all the structure to get it done!
product :: (S.Storage s, Set.Enumerable l, Eq l) => Sp f s l Int -> Int
product sp = elim k (forgetShape sp)
  where k = elimE $ \s -> MS.fold (*) 0 $ Set.smap snd s
