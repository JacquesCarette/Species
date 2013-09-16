{-# LANGUAGE ConstraintKinds #-}
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
data Sp f l a = Struct { _shape ::  f l, _elts :: V.Vec (Size l) a }
  deriving Show

makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

-- | Structures can be relabelled; /i.e./ isomorphisms between label
--   sets induce isomorphisms between labelled structures.
relabelI :: (Finite l1, Finite l2, BFunctor f)
         => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabelI i =
  case isoPresSize i of
    Refl -> iso (\(Struct s es) -> Struct (view (bmap i) s) es)
                (\(Struct s es) -> Struct (view (bmap (from i)) s) es)

-- | A version of 'relabelI' which returns a function instead of an
--   isomorphism, which is sometimes more convenient.
relabel :: (Finite l1, Finite l2, BFunctor f)
        => (l1 <-> l2) -> Sp f l1 a -> Sp f l2 a
relabel = view . relabelI

instance Functor (Sp f l) where
  fmap = over (elts . mapped)

------------------------------------------------------------
--  Reshaping

-- | Structures can also be /reshaped/: isomorphisms between species
--   induce isomorphisms between labelled structures.
reshapeI :: Finite l => (f <--> g) -> (Sp f l a <-> Sp g l a)
reshapeI i = liftIso shape shape i

-- | A version of 'reshapeI' which returns a function instead of an
--   isomorphism, which is sometimes more convenient.
reshape :: Finite l => (f --> g) -> Sp f l a -> Sp g l a
reshape r = over shape r

------------------------------------------------------------
--  Existentially labelled structures

-- | Labelled structures whose label type has been existentially
--   hidden.  Note that we need to package up an @Eq@ constraint on the
--   labels, otherwise we can't really do anything with them and we
--   might as well just not have them at all.
data Sp' f a where
  SpEx :: (Finite l, Eq l) => Sp f l a -> Sp' f a

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
-- JC: can't we pull a 'natty' here too?

-- e' :: [a] -> Sp' E a
-- e' as =
--   case V.fromList as of
--     (V.SomeVec (v :: Vec n a)) -> SpEx (Struct (e_ :: E (Fin n)) v)

-- u ---------------------------------------------

-- Note how this is essentially the Store Comonad.
u :: Finite l => (l -> a) -> l -> Sp U l a
u f x = Struct (u_ x) (fmap f V.enumerate)

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

prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
     => Sp f l1 a -> Sp g l2 a -> Sp (f * g) (Either l1 l2) a
prod (Struct sf esf) (Struct sg esg) = Struct (prod_ sf sg)
                                              (V.append esf esg)

prod' :: Sp' f a -> Sp' g a -> Sp' (f * g) a
prod' (SpEx f) (SpEx g) = SpEx (prod f g)

-- Cartesian product -----------------------------

-- | Superimpose a new shape atop an existing structure, with the
--   structure on the left.
cprodL :: Sp f l a -> g l -> Sp (f # g) l a
cprodL (Struct sf es) sg = Struct (cprod_ sf sg) es

-- | Superimpose a new shape atop an existing structure, with the
--   structure on the right.
cprodR :: f l -> Sp g l a -> Sp (f # g) l a
cprodR sf (Struct sg es) = Struct (cprod_ sf sg) es

-- | Decompose a Cartesian product structure.  Inverse to `cprodL`.
decompL :: Sp (f # g) l a -> (Sp f l a, g l)
decompL (Struct (CProd fl gl) es) = (Struct fl es, gl)

-- | Decompose a Cartesian product structure.  Inverse to `cprodR`.
decompR :: Sp (f # g) l a -> (f l, Sp g l a)
decompR (Struct (CProd fl gl) es) = (fl, Struct gl es)

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

-- | 'compA' can be seen as a generalized version of the 'Applicative'
--   method '<*>'. Unlike 'compJ', there is no dependent variant of 'compA':
--   we only get to provide a single @g@-structure which is copied into
--   all the locations of the @f@-structure, so all the label types must
--   be the same; they cannot depend on the labels of the @f@-structure.
compA :: (Eq l1, Finite l1, Eq l2) => Sp f l1 (a -> b) -> Sp g l2 a -> Sp (Comp f g) (l1,l2) b
compA spf spg = compJ ((<$> spg) <$> spf)

-- | A variant of 'compA', interdefinable with it.
compAP :: (Eq l1, Finite l1, Eq l2) => Sp f l1 a -> Sp g l2 b -> Sp (Comp f g) (l1,l2) (a,b)
compAP spf spg = compA (fmap (,) spf) spg

-- | 'compJ' and 'compJ'' are like generalized versions of the 'Monad'
--   function 'join'.
--
--   'compJ' is a restricted form of composition where the substructures
--   are constrained to all have the same label type.
compJ :: forall f l1 g l2 a. (Eq l1, Finite l1, Eq l2)
      => Sp f l1 (Sp g l2 a) -> Sp (Comp f g) (l1,l2) a
compJ (Struct f_ es)
    = case mapRep l1Size (Proxy :: Proxy g) (Proxy :: Proxy l2) of
        Refl ->
          allRep l1Size (Proxy :: Proxy Eq) (Proxy :: Proxy l2) $
          Struct (Comp f_ (lpRep l1Size (Proxy :: Proxy l2)) gShps' pf)
                 (V.concat gElts)
  where
    l1Size              = size (Proxy :: Proxy l1)
    (gShps, gElts)      = V.unzip (fmap unSp es)
    gShps'              = V.toHVec gShps
    unSp (Struct sh es') = (sh, es')
    pf                  :: Sum (Replicate (Size l1) l2) <-> (l1, l2)
    pf                  = sumRepIso (Proxy :: Proxy l1)

-- | 'compJ'' is a fully generalized version of 'join'.
--
--   Ideally the type of 'compJ'' would be a dependent version of the
--   type of 'compJ', where @l2@ can depend on @l1@.  Indeed, I expect
--   that in a true dependently typed language we can write that type
--   directly.  However, we can't express that in Haskell, so instead
--   we use existential quantification.
compJ' :: forall f l g a. (Eq l, Finite l) => Sp f l (Sp' g a) -> Sp' (Comp f g) a
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
  UZSS :: (Eq (Sum ls), Finite (Sum ls), All Eq ls)
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

