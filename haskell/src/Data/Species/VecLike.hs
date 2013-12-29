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
-- let's try to implement the 'back half' first: given a species of 
-- shape L#Part, extract a filtered list
extract :: (S.LabelledStorage s, Set.Enumerable l, Eq l) => 
    Sp (L.L # Part) s l a -> [a]
extract sp = 
  -- because of existential, it is very hard to rewrite the code below
  -- in a less `inline' style.
  let (lsp, part) = decompL sp
  in gelim (L.gelimList [] 
      (\(l,a) r -> 
        case part of 
          Prod _ _ eiso ->
            case view (from eiso) l of
              Left _  -> a : r
              Right _ ->     r  )) lsp

-- Victory!
-- The *code* below is quite ugly, but that is because we have to have a way
-- to be explicit about all our choices.  Our setup is very polymorphic,
-- and we need to pin all these things down to get a runnable routine.
filter' :: forall a. (a -> Bool) -> [a] -> [a]
filter' p lst = 
  case Vec.fromList lst of
    Vec.SomeVec v -> 
      let n = Vec.size v
          sp = fromVec v
          e :: forall n. N.Natural n => Sp (L.L # Part) (->) (F.Fin n) a -> [a]
          e = extract
          f :: forall n. N.Natural n => Sp L.L (->) (F.Fin n) a -> (a -> Bool) -> Sp (L.L # Part) (->) (F.Fin n) a
          f = filter
      in N.natty n $ e $ f sp p
