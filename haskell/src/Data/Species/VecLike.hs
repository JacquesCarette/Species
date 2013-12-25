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
                sn = N.natty n $ Set.enumerate $ finite_Fin
                sm = N.natty m $ Set.enumerate $ finite_Fin

-- We need an Enumerable constraint
filter :: (S.Storage s, Set.Enumerable l, Eq l) => Sp f s l a -> (a -> Bool) -> Sp (f # Part) s l a
filter (Struct f stor) p = Struct (cprod_ f k) stor
  where sel = S.smap p stor
        k = part_ Set.enumS Set.enumS
                  (iso (\l -> case l of {Left a -> a; Right a -> a}) 
                       (\l -> if (S.index sel l) then Left l else Right l) )
