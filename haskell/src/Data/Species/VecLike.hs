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
import           Control.Lens (iso)
import           Data.Type.Equality

import qualified Data.Fin                 as F
import           Data.Fin.Isos (finSum, finSum')
import           Data.Iso
import           Data.Finite
import           Data.Species.Shape
import           Data.Species.Types
import qualified Data.Type.Nat            as N
import           Data.Type.Nat.Inequality
import           Data.Type.Nat.Minus
import qualified Data.Storage             as S
import qualified Data.Set.Abstract        as Set
import qualified Data.Species.List        as L


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

-- We can do this with an Enumerable constraint, which is less `leaky'
-- than a Finite proof.
filter :: (S.Storage s, Set.Enumerable l, Eq l) => 
          Sp f s l a -> (a -> Bool) -> Sp (f # Part) s l a
filter (Struct f stor) p = Struct (cprod_ f k) stor
  where sel = S.smap p stor
        k = part_ Set.enumS Set.enumS
                  (iso (\l -> case l of {Left a -> a; Right a -> a}) 
                       (\l -> if (S.index sel l) then Left l else Right l) )

-- One question still nags: is the above really filter?  In other words,
-- could we implement Prelude.filter with the above?
{-
filter' :: forall a. (a -> Bool) -> [a] -> [a]
filter' pr l = undefined
  where sp :: Sp L.L (->) l a -- pick an explicit Storage
        sp = case (L.fromList l) of SpEx s -> s
        res = filter sp pr
-}
