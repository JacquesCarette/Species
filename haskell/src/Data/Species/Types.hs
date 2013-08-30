{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE Rank2Types                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Species.Types where

import           Control.Lens hiding (cons)
import           Data.Proxy
import           Data.Type.Equality

import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Functor ((<$>))
import           Data.Species.Shape
import           Data.Type.List
import           Data.Type.Nat
import qualified Data.Vec     as V

------------------------------------------------------------
-- Labelled structures

-- A species is a labelled shape paired with a map from labels to data
-- values.  Since label types are required to be constructively
-- finite, that is, come with an isomorphism to Fin n for some n, we
-- can represent the map as a length-n vector.
data Sp f l a = Struct { _shape ::  f l, _elts :: V.Vec (Size l) a }
  deriving Show

makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

-- Species structures can also be relabelled.
relabelI :: (Finite l1, Finite l2, BFunctor f)
         => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabelI i =
  case isoPresSize i of
    Refl -> iso (\(Struct s es) -> Struct (view (bmap i) s) es)
                (\(Struct s es) -> Struct (view (bmap (from i)) s) es)

relabel :: (Finite l1, Finite l2, BFunctor f)
        => (l1 <-> l2) -> Sp f l1 a -> Sp f l2 a
relabel = view . relabelI

instance Functor (Sp f l) where
  fmap = over (elts . mapped)

instance Functor (Sp' f) where
  fmap f (SpEx s) = SpEx (fmap f s)

------------------------------------------------------------
--  Reshaping

reshapeI :: Finite l => (f <--> g) -> (Sp f l a <-> Sp g l a)
reshapeI i = liftIso shape shape i

reshape :: Finite l => (f --> g) -> Sp f l a -> Sp g l a
reshape r = over shape r

------------------------------------------------------------
--  Existentially labelled structures

-- We need to package up an Eq constraint on the labels, otherwise we
-- can't really do anything with them and we might as well just not
-- have them at all.

data Sp' f a where
  SpEx :: (Finite l, Eq l) => Sp f l a -> Sp' f a

-- Or we can package up an Ord constraint and get L-species
-- structures.

data LSp' f a where
  LSpEx :: Ord l => Sp f l a -> LSp' f a

-- One -------------------------------------------

one :: Sp One (Fin Z) a
one = Struct one_ V.VNil

one' :: Sp' One a
one' = SpEx one

-- X ---------------------------------------------

x :: a -> Sp X (Fin (S Z)) a
x a = Struct x_ (V.singleton a)

x' :: a -> Sp' X a
x' = SpEx . x

-- E ---------------------------------------------

e :: Finite l => (l -> a) -> Sp E l a
e f = Struct e_ (fmap f V.enumerate)

-- Argh, this needs a Natural constraint, but adding one to SomeVec
-- ends up infecting everything in a very annoying way.

-- e' :: [a] -> Sp' E a
-- e' as =
--   case V.fromList as of
--     (V.SomeVec (v :: Vec n a)) -> SpEx (Struct (e_ :: E (Fin n)) v)

-- Sum -------------------------------------------

inl :: Sp f l a -> Sp (f + g) l a
inl = shape %~ inl_

inl' :: Sp' f a -> Sp' (f + g) a
inl' (SpEx s) = SpEx (inl s)

inr :: Sp g l a -> Sp (f + g) l a
inr = shape %~ inr_

inr' :: Sp' g a -> Sp' (f + g) a
inr' (SpEx s) = SpEx (inr s)

-- Product ---------------------------------------

prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
     => Sp f l1 a -> Sp g l2 a -> Sp (f * g) (Either l1 l2) a
prod (Struct sf esf) (Struct sg esg) = Struct (prod_ sf sg)
                                              (V.append esf esg)

prod' :: Sp' f a -> Sp' g a -> Sp' (f * g) a
prod' (SpEx f) (SpEx g) = SpEx (prod f g)

-- Cartesian product -----------------------------

-- Superimpose a new shape atop an existing structure from the left
cprodL :: f l -> Sp g l a -> Sp (f # g) l a
cprodL sf (Struct sg es) = Struct (cprod_ sf sg) es

-- Same thing from the right
cprodR :: Sp f l a -> g l -> Sp (f # g) l a
cprodR (Struct sf es) sg = Struct (cprod_ sf sg) es

-- Differentiation -------------------------------

d :: Sp f (Maybe l) a -> Sp (D f) l a
d (Struct s es) = Struct (d_ s) (V.tail es)

-- No d' operation since it really does depend on the labels

-- Pointing --------------------------------------

p :: l -> Sp f l a -> Sp (P f) l a
p l (Struct s es) = Struct (p_ l s) es

-- No p' operation---it again depends on the labels

-- Partition   -----------------------------------

-- the constraint that Plus (Size l1) (Size l2) ~ Size l
-- should follow from having an iso between Either l1 l2 and l, but
-- it is unclear to me (JC) how to derive that
part :: forall l1 l2 l a . (Finite l1, Finite l2, Plus (Size l1) (Size l2) ~ Size l) =>
    (l1 -> a) -> (l2 -> a) -> (Either l1 l2 <-> l) -> Sp Part l a
part f g i = Struct (part_ i) (V.append v1 v2)
              where
                v1 :: V.Vec (Size l1) a
                v1 = fmap f $ V.enumerate
                v2 :: V.Vec (Size l2) a
                v2 = fmap g $ V.enumerate

-- It is not clear that we can create a part' because this witnesses a subset
-- relation on labels, which seems difficult to abstract

-- Composition -----------------------------------

-- compA is a generalized version of (<*>). Unlike compJ, there is no
-- dependent variant of compA: we only get to provide a single
-- g-structure which is copied into all the locations of the
-- f-structure, so all the label types must be the same; they cannot
-- depend on the labels of the f-structure.

compA :: (Eq l1, Finite l1) => Sp f l1 (a -> b) -> Sp g l2 a -> Sp (Comp f g) (l1,l2) b
compA spf spg = compJ ((<$> spg) <$> spf)

-- compAP is a generalized version of an alternate formulation of
-- Applicative.

compAP :: (Eq l1, Finite l1) => Sp f l1 a -> Sp g l2 b -> Sp (Comp f g) (l1,l2) (a,b)
compAP spf spg = compA (fmap (,) spf) spg

-- compJ and compJ' are like generalized versions of 'join'.

-- compJ is a restricted form of composition where the substructures
-- are constrained to all have the same label type.
compJ :: forall f l1 g l2 a. (Eq l1, Finite l1) => Sp f l1 (Sp g l2 a) -> Sp (Comp f g) (l1,l2) a
compJ (Struct f_ es)
    = case mapRep l1Size (Proxy :: Proxy g) (Proxy :: Proxy l2) of
        Refl ->
          Struct (Comp f_ (lpRep l1Size (Proxy :: Proxy l2)) gShps' pf)
                 (V.concat gElts)
  where
    l1Size              = size (Proxy :: Proxy l1)
    (gShps, gElts)      = V.unzip (fmap unSp es)
    gShps'              = V.toHVec gShps
    unSp (Struct sh es') = (sh, es')
    pf                  :: Sum (Replicate (Size l1) l2) <-> (l1, l2)
    pf                  = sumRepIso (Proxy :: Proxy l1)

-- Ideally the type of compJ' would be a dependent version of the type
-- of compJ, where l2 can depend on l1.  Indeed, I expect that in a
-- true dependently typed language we can write that type directly.
-- However, we can't express that in Haskell, so instead we use
-- existential quantification.
compJ' :: forall f l g a. Eq l => Sp f l (Sp' g a) -> Sp' (Comp f g) a
compJ' (Struct f_ es)
  = case unzipSpSp' es of
      UZSS ls gShps gElts ->
        SpEx (Struct
               (Comp f_ ls gShps id)
               (V.hconcat (Proxy :: Proxy g) ls gElts)
             )

  -- If you squint really hard, you can see that the implementations
  -- of compJ and compJ' are structurally identical, but with a bunch
  -- of extra machinery thrown in to convince the typechecker, in
  -- fact, different machinery in each case: in the case of compJ, we
  -- have to do some work to replicate the second label type and show
  -- that iterated sum is the same as a product.  In the case of
  -- compJ', we have to work to maintain existentially-quantified
  -- heterogeneous lists of types and carefully preserve knowledge
  -- about which types are equal.

-- A data structure to represent an "unzipped" Sp(Sp')-thing: a vector
-- of g-structures paired with a vector of element vectors, with the
-- list of label types existentially hidden.
data UnzippedSpSp' n g a where
  UZSS :: (Eq (Sum ls), Finite (Sum ls))
       => LProxy n ls    -- We need an LProxy so the typechecker can
                         -- actually infer the label types (the only
                         -- other occurrences of ls are buried inside
                         -- type functions which we know are injective
                         -- but GHC doesn't) and to drive recursion
                         -- over the vectors.
       -> V.HVec n (Map g ls)           -- vector of g-structures
       -> V.HVec n (V.VecsOfSize ls a)  -- vector of element vectors
       -> UnzippedSpSp' n g a

unzipSpSp' :: V.Vec n (Sp' g a) -> UnzippedSpSp' n g a
unzipSpSp' V.VNil = UZSS LNil V.HNil V.HNil
unzipSpSp' (V.VCons (SpEx (Struct (gl :: g l) v)) sps) =
  case unzipSpSp' sps of
    UZSS prox gls evs
      -> UZSS (LCons (Proxy :: Proxy l) prox) (V.HCons gl gls) (V.HCons v evs)

-- Functor composition ---------------------------

-- XXX todo

-- Cardinality restriction -----------------------

sized :: Finite l => Sp f l a -> Sp (OfSize (Size l) f) l a
sized (Struct s es) = Struct (sized_ s) es
