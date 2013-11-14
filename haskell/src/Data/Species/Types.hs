{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE EmptyDataDecls             #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module Data.Species.Types
    ( -- * Labelled structures

      Sp(..), shape, elts

      -- * Relabelling and reshaping

    , relabelI, relabel
    , reshapeI, reshape

      -- * Existentially quantified structures

    , Sp'(..), withSp

      -- * Introduction forms
      -- ** Unit
    , one, one'
      -- ** Singleton
    , x, x'
      -- ** Bags
    , e
      -- ** Sum
    , inl, inr, inl', inr'
      -- ** Product
    , prod, prod'
      -- ** Cartesian product
    , cprodL, cprodR, decompL, decompR, projL, projR, editL, editR
      -- ** Differentiation
    , d
      -- ** Pointing
    , p
      -- ** Partition
    , part
      -- ** Composition
    , compA, compAP, compJ, compJ', compJ''
      -- ** Cardinality restriction
    , sized
    )
    where

import           Control.Arrow (first, second)
import           Control.Lens hiding (cons)
import           Data.Proxy
import           Data.Type.Equality

import           Data.Iso
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

-- | A species is a labelled shape paired with a map from labels to data
--   values.  Since label types are required to be constructively
--   finite, that is, come with an isomorphism to @'Fin' n@ for some n, we
--   can represent the map as a length-@n@ vector.
data Sp f l a = Struct { _shape ::  f l, _elts :: V.Vec (Size l) a, _finpf :: Finite l }

makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

-- | Structures can be relabelled; /i.e./ isomorphisms between label
--   sets induce isomorphisms between labelled structures.
relabelI :: (BFunctor f, HasSize l1, HasSize l2, Eq l1, Eq l2)
         => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabelI i =
  case isoPresSize i of
    Refl -> iso (\(Struct s es pf) -> Struct (view (bmap i) s) es (finConv i pf))
                (\(Struct s es pf) -> Struct (view (bmap (from i)) s) es (finConv (from i) pf))

-- | A version of 'relabelI' which returns a function instead of an
--   isomorphism, which is sometimes more convenient.
relabel :: (BFunctor f, HasSize l1, HasSize l2, Eq l1, Eq l2)
        => (l1 <-> l2) -> Sp f l1 a -> Sp f l2 a
relabel = view . relabelI

instance Functor (Sp f l) where
  fmap = over (elts . mapped)

------------------------------------------------------------
--  Reshaping

-- | Structures can also be /reshaped/: isomorphisms between species
--   induce isomorphisms between labelled structures.
reshapeI :: Eq l => (f <--> g) -> (Sp f l a <-> Sp g l a)
reshapeI i = liftIso shape shape i

-- | A version of 'reshapeI' which returns a function instead of an
--   isomorphism, which is sometimes more convenient.
reshape :: Eq l => (f --> g) -> Sp f l a -> Sp g l a
reshape r = over shape r

------------------------------------------------------------
--  Existentially labelled structures

-- | Labelled structures whose label type has been existentially
--   hidden.  Note that we need to package up an @Eq@ constraint on the
--   labels, otherwise we can't really do anything with them and we
--   might as well just not have them at all.
data Sp' f a where
  SpEx :: (HasSize l, Eq l) => Sp f l a -> Sp' f a

withSp :: (forall l. Sp f l a -> Sp g l b) -> Sp' f a -> Sp' g b
withSp q sp' = case sp' of SpEx sp -> SpEx (q sp)

instance Functor (Sp' f) where
  fmap f = withSp (fmap f)

-- Or we can package up an Ord constraint and get L-species
-- structures.

data LSp' f a where
  LSpEx :: Ord l => Sp f l a -> LSp' f a

-- One -------------------------------------------

one :: Sp One (Fin Z) a
one = Struct one_ V.VNil finite_Fin

one' :: Sp' One a
one' = SpEx one

-- X ---------------------------------------------

x :: a -> Sp X (Fin (S Z)) a
x a = Struct x_ (V.singleton a) finite_Fin

x' :: a -> Sp' X a
x' = SpEx . x

-- E ---------------------------------------------

e :: Finite l -> (l -> a) -> Sp E l a
e fin f = Struct (e_ fin) (fmap f $ V.enumerate fin) fin

-- Argh, this needs a Natural constraint, but adding one to SomeVec
-- ends up infecting everything in a very annoying way.
-- JC: can't we pull a 'natty' here too?

-- e' :: [a] -> Sp' E a
-- e' as =
--   case V.fromList as of
--     (V.SomeVec (v :: V.Vec n a)) -> SpEx (Struct (e_ (finite_Fin) :: E (Fin n)) v finite_Fin)

-- u ---------------------------------------------

-- Note how this is essentially the Store Comonad.
u :: Finite l -> (l -> a) -> l -> Sp U l a
u fin f x = Struct (u_ x) (fmap f $ V.enumerate fin) fin

-- Sum -------------------------------------------

inl :: Sp f l a -> Sp (f + g) l a
inl = shape %~ inl_

inl' :: Sp' f a -> Sp' (f + g) a
inl' = withSp inl

inr :: Sp g l a -> Sp (f + g) l a
inr = shape %~ inr_

inr' :: Sp' g a -> Sp' (f + g) a
inr' = withSp inr

-- Product ---------------------------------------

prod :: (Eq l1, Eq l2)
     => Sp f l1 a -> Sp g l2 a -> Sp (f * g) (Either l1 l2) a
prod (Struct sf esf finf) (Struct sg esg fing) = 
    Struct (prod_ sf sg) (V.append esf esg) (finite_Either finf fing)

prod' :: Sp' f a -> Sp' g a -> Sp' (f * g) a
prod' (SpEx f) (SpEx g) = SpEx (prod f g)

-- Cartesian product -----------------------------

-- | Superimpose a new shape atop an existing structure, with the
--   structure on the left.
cprodL :: Sp f l a -> g l -> Sp (f # g) l a
cprodL (Struct sf es finf) sg = Struct (cprod_ sf sg) es finf

-- | Superimpose a new shape atop an existing structure, with the
--   structure on the right.
cprodR :: f l -> Sp g l a -> Sp (f # g) l a
cprodR sf (Struct sg es finf) = Struct (cprod_ sf sg) es finf

-- | Decompose a Cartesian product structure.  Inverse to `cprodL`.
decompL :: Sp (f # g) l a -> (Sp f l a, g l)
decompL (Struct (CProd fl gl) es finf) = (Struct fl es finf, gl)

-- | Decompose a Cartesian product structure.  Inverse to `cprodR`.
decompR :: Sp (f # g) l a -> (f l, Sp g l a)
decompR (Struct (CProd fl gl) es fing) = (fl, Struct gl es fing)

-- | Project out the left structure from a Cartesian product.
projL ::  Sp (f # g) l a -> Sp f l a
projL = fst . decompL

-- | Project out the right structure from a Cartesian product.
projR ::  Sp (f # g) l a -> Sp g l a
projR = snd . decompR

-- | Apply a function to the left-hand structure of a Cartesian
-- product.
editL :: (Sp f l a -> Sp f l b) -> (Sp (f # g) l a -> Sp (f # g) l b)
editL f = uncurry cprodL . first f . decompL

-- | Apply a function to the right-hand structure of a Cartesian
-- product.
editR :: (Sp g l a -> Sp g l b) -> (Sp (f # g) l a -> Sp (f # g) l b)
editR f = uncurry cprodR . second f . decompR

-- Differentiation -------------------------------

d :: (Eq l, HasSize l) => Sp f (Maybe l) a -> Sp (D f) l a
d (Struct s (V.VCons eHead es) finf@(F i))
  = Struct (d_ s) es' (finite_predMaybe finf)
  where
    es' = case view (from i) Nothing of
             FZ     -> es
             FS idx -> snd (V.replace idx eHead es)

-- No d' operation since it really does depend on the labels

-- Pointing --------------------------------------

p :: l -> Sp f l a -> Sp (P f) l a
p l (Struct s es finf) = Struct (p_ l s) es finf

-- No p' operation---it again depends on the labels

-- Partition   -----------------------------------

-- the constraint that Plus (Size l1) (Size l2) ~ Size l
-- should follow from having an iso between Either l1 l2 and l, but
-- it is unclear to me (JC) how to derive that
part :: forall l1 l2 l a . (Eq l, HasSize l, Plus (Size l1) (Size l2) ~ Size l) =>
    Finite l1 -> Finite l2 ->
    (l1 -> a) -> (l2 -> a) -> (Either l1 l2 <-> l) -> Sp Part l a
part finf fing f g i = Struct (part_ finf fing i) (V.append v1 v2) (finConv i $ finite_Either finf fing)
                         where
                           v1 :: V.Vec (Size l1) a
                           v1 = fmap f $ V.enumerate finf
                           v2 :: V.Vec (Size l2) a
                           v2 = fmap g $ V.enumerate fing

-- It is not clear that we can create a part' because this witnesses a subset
-- relation on labels, which seems difficult to abstract

-- Composition -----------------------------------

-- | 'compA' can be seen as a generalized version of the 'Applicative'
--   method '<*>'. Unlike 'compJ', there is no dependent variant of 'compA':
--   we only get to provide a single @g@-structure which is copied into
--   all the locations of the @f@-structure, so all the label types must
--   be the same; they cannot depend on the labels of the @f@-structure.
compA :: (Eq l1, Eq l2, HasSize l1, HasSize l2) => Sp f l1 (a -> b) -> Sp g l2 a -> Sp (Comp f g) (l1,l2) b
compA spf spg = compJ ((<$> spg) <$> spf)

-- | A variant of 'compA', interdefinable with it.
compAP :: (Eq l1, Eq l2, HasSize l1, HasSize l2) => Sp f l1 a -> Sp g l2 b -> Sp (Comp f g) (l1,l2) (a,b)
compAP spf spg = compA (fmap (,) spf) spg

-- | 'compJ' and 'compJ'' are like generalized versions of the 'Monad'
--   function 'join'.
--
--   'compJ' is a restricted form of composition where the substructures
--   are constrained to all have the same label type.

compJ :: forall f l1 g l2 a. (Eq l1, Eq l2, HasSize l1, HasSize l2)
      => Sp f l1 (Sp g l2 a) -> Sp (Comp f g) (l1,l2) a
compJ (Struct f_ es finl1@(F isol1))
    = case mapRep l1Size (Proxy :: Proxy g) (Proxy :: Proxy l2) of
        Refl ->
          allRep l1Size (Proxy :: Proxy Eq) (Proxy :: Proxy l2) $
          Struct (Comp finl1 f_ (lpRep l1Size (Proxy :: Proxy l2)) gShps' pf)
                 (V.concat gElts) finl1l2
  where
    l1Size                 = size finl1
    (gShps, gElts, finPfs) = V.unzip3 (fmap unSp es)
    gShps'                 = V.toHVec gShps
    unSp (Struct sh es' f) = (sh, es', f)
    pf                     :: Sum (Replicate (Size l1) l2) <-> (l1, l2)
    pf                     = sumRepIso finl1
    finl1l2 :: Finite (l1,l2)
    finl1l2 = finConv (liftIso _1 _1 isol1) (V.finite_cat finPfs)

-- | 'compJ'' is a fully generalized version of 'join'.
--
--   Ideally the type of 'compJ'' would be a dependent version of the
--   type of 'compJ', where @l2@ can depend on @l1@.  Indeed, I expect
--   that in a true dependently typed language we can write that type
--   directly.  However, we can't express that in Haskell, so instead
--   we use existential quantification.
compJ' :: forall f l g a. (Eq l) => Sp f l (Sp' g a) -> Sp' (Comp f g) a
compJ' (Struct f_ es finl)
  = case unzipSpSp' es of
      UZSS ls gShps gElts finPfs ->
        SpEx (Struct
               (Comp finl f_ ls gShps id)
               (V.hconcat (Proxy :: Proxy g) ls gElts)
               (V.finite_hcat ls finPfs)
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

-- | For convenience, a variant of 'compJ'' which takes an
--   existentially labelled structure as input.
compJ'' :: forall f g a. Sp' f (Sp' g a) -> Sp' (Comp f g) a
compJ'' sp' =
  case sp' of
    SpEx sp -> compJ' sp

-- A data structure to represent an "unzipped" Sp(Sp')-thing: a vector
-- of g-structures paired with a vector of element vectors, with the
-- list of label types existentially hidden.
data UnzippedSpSp' n g a where
  UZSS :: (Eq (Sum ls), HasSize (Sum ls), All Eq ls)
       => LProxy n ls    -- We need an LProxy so the typechecker can
                         -- actually infer the label types (the only
                         -- other occurrences of ls are buried inside
                         -- type functions which we know are injective
                         -- but GHC doesn't) and to drive recursion
                         -- over the vectors.
       -> V.HVec n (Map g ls)           -- vector of g-structures
       -> V.HVec n (V.VecsOfSize ls a)  -- vector of element vectors
       -> V.HVec n (Map Finite ls)
       -> UnzippedSpSp' n g a

unzipSpSp' :: V.Vec n (Sp' g a) -> UnzippedSpSp' n g a
unzipSpSp' V.VNil = UZSS LNil V.HNil V.HNil V.HNil
unzipSpSp' (V.VCons (SpEx (Struct (gl :: g l) v finl)) sps) =
  case unzipSpSp' sps of
    UZSS prox gls evs finPfs
      -> UZSS (LCons (Proxy :: Proxy l) prox) (V.HCons gl gls) (V.HCons v evs) (V.HCons finl finPfs)

-- Functor composition ---------------------------

-- XXX todo

-- Cardinality restriction -----------------------

sized :: Sp f l a -> Sp (OfSize (Size l) f) l a
sized (Struct s es finl) = Struct (sized_ finl s) es finl

