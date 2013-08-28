{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE EmptyDataDecls      #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE Rank2Types          #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Species.Types where

import           Control.Lens hiding (cons)
import           Data.BFunctor
import           Data.Fin
import           Data.Finite
import           Data.Functor ((<$>))
import           Data.Proxy
import qualified Data.Set.Abstract          as S
import           Data.Type.Equality
import           Data.Type.List
import           Data.Type.Nat
import qualified Data.Vec     as V

import           Unsafe.Coerce

------------------------------------------------------------
--  Labelled shapes and data structures

-- A labelled shape is a shape filled with a finite set of labels
type Shape f l = f l

-- Shapes with an existentially quantified label type.
data Shape' :: (* -> *) -> * where
  Shape' :: (Eq l, Finite l) => Shape f l -> Shape' f

-- A species is a labelled shape paired with a map from labels to data
-- values.  Since label types are required to be constructively
-- finite, that is, come with an isomorphism to Fin n for some n, we
-- can represent the map as a length-n vector.
data Sp f l a = Struct { _shape :: Shape f l, _elts :: V.Vec (Size l) a }
  deriving Show

makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

relabelShape' :: (Finite l1, Finite l2, BFunctor f)
              => (l1 <-> l2) -> (Shape f l1 <-> Shape f l2)
relabelShape' = bmap

relabelShape :: (Finite l1, Finite l2, BFunctor f)
             => (l1 <-> l2) -> Shape f l1 -> Shape f l2
relabelShape = view . bmap

-- Species structures can also be relabelled.
relabel' :: (Finite l1, Finite l2, BFunctor f)
         => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabel' i =
  case isoPresSize i of
    Refl -> iso (\(Struct s es) -> Struct (view (bmap i) s) es)
                (\(Struct s es) -> Struct (view (bmap (from i)) s) es)

relabel :: (Finite l1, Finite l2, BFunctor f)
        => (l1 <-> l2) -> Sp f l1 a -> Sp f l2 a
relabel = view . relabel'

instance Functor (Sp f l) where
  fmap = over (elts . mapped)

instance Functor (Sp' f) where
  fmap f (SpEx s) = SpEx (fmap f s)

------------------------------------------------------------
--  Reshaping

reshape' :: Finite l => (f <--> g) -> (Sp f l a <-> Sp g l a)
reshape' i = liftIso shape shape i

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

------------------------------------------------------------
--  Shape functors, along with introduction forms
--
-- Each introduction form gives a "canonically labeled" structure;
-- relabeling can be used to convert to some other labeling.

-- Zero ------------------------------------------

data Zero :: * -> *
  deriving Functor

instance BFunctor Zero

absurdZ :: Zero l -> a
absurdZ = unsafeCoerce

-- One -------------------------------------------

data One l = One (Fin Z <-> l)

instance Show (One l) where
  show _ = "One"

instance BFunctor One where
  bmap i = iso (\(One vl ) -> One (vl .i))
               (\(One vl') -> One (vl'.from i))

oneSh :: Shape One (Fin Z)
oneSh = One id

one :: Sp One (Fin Z) a
one = Struct oneSh V.VNil

one' :: Sp' One a
one' = SpEx one

-- X ---------------------------------------------

data X l = X (Fin (S Z) <-> l)

instance Show l => Show (X l) where
  show (X i) = show (view i FZ)

instance BFunctor X where
  bmap i = iso (\(X ul ) -> X (ul .i))
               (\(X ul') -> X (ul'.from i))

xSh :: Shape X (Fin (S Z))
xSh = X id

x :: a -> Sp X (Fin (S Z)) a
x a = Struct xSh (V.singleton a)

x' :: a -> Sp' X a
x' = SpEx . x

-- E ---------------------------------------------

newtype E (l :: *) = E (S.Set l)
  deriving (BFunctor, Show)

eSh :: Finite l => Shape E l
eSh = E S.enumerate

e :: Finite l => (l -> a) -> Sp E l a
e f = Struct eSh (fmap f V.enumerate)

-- Argh, this needs a Natural constraint, but adding one to SomeVec
-- ends up infecting everything in a very annoying way.

-- e' :: [a] -> Sp' E a
-- e' as =
--   case V.fromList as of
--     (V.SomeVec (v :: Vec n a)) -> SpEx (Struct (eSh :: Shape E (Fin n)) v)

-- Sum -------------------------------------------

infixl 6 +
data (f + g) (l :: *) = Inl (f l)
                      | Inr (g l)
  deriving Functor

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g, Finite l, Finite l')
               => (l <-> l') -> (f + g) l -> (f + g) l'
      applyIso i' (Inl f) = Inl (view (bmap i') f)
      applyIso i' (Inr g) = Inr (view (bmap i') g)

inlSh :: Shape f l -> Shape (f + g) l
inlSh = Inl

inl :: Sp f l a -> Sp (f + g) l a
inl = shape %~ inlSh

inl' :: Sp' f a -> Sp' (f + g) a
inl' (SpEx s) = SpEx (inl s)

inrSh :: Shape g l -> Shape (f + g) l
inrSh = Inr

inr :: Sp g l a -> Sp (f + g) l a
inr = shape %~ inrSh

inr' :: Sp' g a -> Sp' (f + g) a
inr' (SpEx s) = SpEx (inr s)

-- parallel sum? ---------------------------------

-- No idea whether this is useful for anything but it seems to be
-- suggested by parallels with linear logic.  It's dual to product
-- just as Cartesian product is dual to sum.  It's pretty weird.

data (f +? g) l where
  ParSum :: (Either (f l1) (g l2)) -> (Either l1 l2 <-> l) -> (f +? g) l

instance (BFunctor f, BFunctor g) => BFunctor (f +? g) where
  bmap i = iso (\(ParSum fg pf) -> ParSum fg (pf.i))
               (\(ParSum fg pf) -> ParSum fg (pf.from i))

-- pInlSh :: Shape f l1 -> Shape (f +? g) (Either l1 l2)
-- pInlSh (Shape n f) = Shape n (ParSum (Left f) id)

-- pInl :: Sp f l1 a -> Sp (f +? g) (Either l1 l2) a
-- pInl (Struct s es) = Struct (pInlSh s) (M.mapLabels Left es)

-- This doesn't typecheck because l2 is completely ambiguous.
-- Fundamentally this is because ParSum is weird.
--
-- pInl' :: Sp' f a -> Sp' (f +? g) a
-- pInl' (SpEx s) = SpEx (pInl s)

-- Product ---------------------------------------

infixl 7 *
data (f * g) l where
  Prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap i = iso (\(Prod f g pf) -> Prod f g (pf.i))
               (\(Prod f g pf) -> Prod f g (pf.from i))

prodSh :: (Eq l1, Finite l1, Eq l2, Finite l2)
       => Shape f l1 -> Shape g l2 -> Shape (f * g) (Either l1 l2)
prodSh f g = Prod f g id

prod :: (Eq l1, Finite l1, Eq l2, Finite l2)
     => Sp f l1 a -> Sp g l2 a -> Sp (f * g) (Either l1 l2) a
prod (Struct sf esf) (Struct sg esg) = Struct (prodSh sf sg)
                                              (V.append esf esg)

prod' :: Sp' f a -> Sp' g a -> Sp' (f * g) a
prod' (SpEx f) (SpEx g) = SpEx (prod f g)

-- Cartesian product -----------------------------

data (f # g) l where
  CProd :: f l -> g l -> (f # g) l

instance (BFunctor f, BFunctor g) => BFunctor (f # g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g, Finite l, Finite l')
               => (l <-> l') -> (f # g) l -> (f # g) l'
      applyIso i' (CProd f g) = CProd (view (bmap i') f) (view (bmap i') g)

instance (Functor f, Functor g) => Functor (f # g) where
  fmap f (CProd f1 f2) = CProd (fmap f f1) (fmap f f2)

cprodSh :: Shape f l -> Shape g l -> Shape (f # g) l
cprodSh f g = CProd f g

-- Superimpose a new shape atop an existing structure from the left
cprodL :: Shape f l -> Sp g l a -> Sp (f # g) l a
cprodL sf (Struct sg es) = Struct (cprodSh sf sg) es

-- Same thing from the right
cprodR :: Sp f l a -> Shape g l -> Sp (f # g) l a
cprodR (Struct sf es) sg = Struct (cprodSh sf sg) es

-- Differentiation -------------------------------

data D f l where
  D :: f l1 -> (l1 <-> Maybe l) -> D f l

instance BFunctor f => BFunctor (D f) where
  bmap i = iso (\(D f pf) -> D f (pf.iMaybe i))
               (\(D f pf) -> D f (pf.iMaybe (from i)))

iMaybe :: (a <-> b) -> (Maybe a <-> Maybe b)
iMaybe i = liftIso _Just _Just i

dSh :: Shape f (Maybe l) -> Shape (D f) l
dSh f = D f id

d :: Sp f (Maybe l) a -> Sp (D f) l a
d (Struct s es) = Struct (dSh s) (V.tail es)

-- No d' operation since it really does depend on the labels

-- Pointing --------------------------------------

data P f l where
  P :: l -> f l -> P f l

instance BFunctor f => BFunctor (P f) where
  bmap i = iso (\(P l f) -> P (view i l) (view (bmap i) f))
               (\(P l f) -> P (view (from i) l) (view (bmap (from i)) f))

pSh :: l -> Shape f l -> Shape (P f) l
pSh l f = P l f

p :: l -> Sp f l a -> Sp (P f) l a
p l (Struct s es) = Struct (pSh l s) es

-- No p' operation---it again depends on the labels

-- Partition   -----------------------------------
-- This can be see as 'just' E * E, but it is useful to give it a name

data Part l where
  Part :: (Finite l1, Finite l2) => S.Set l1 -> S.Set l2 -> (Either l1 l2 <-> l) -> Part l

partSh :: (Finite l1, Finite l2) => (Either l1 l2 <-> l) -> Shape Part l
partSh i = Part S.enumerate S.enumerate i

-- the constraint that Plus (Size l1) (Size l2) ~ Size l
-- should follow from having an iso between Either l1 l2 and l, but
-- it is unclear to me (JC) how to derive that
part :: forall l1 l2 l a . (Finite l1, Finite l2, Plus (Size l1) (Size l2) ~ Size l) =>
    (l1 -> a) -> (l2 -> a) -> (Either l1 l2 <-> l) -> Sp Part l a
part f g i = Struct (partSh i) (V.append v1 v2)
              where
                v1 :: V.Vec (Size l1) a
                v1 = fmap f $ V.enumerate
                v2 :: V.Vec (Size l2) a
                v2 = fmap g $ V.enumerate

instance BFunctor Part where
  bmap i = iso (\(Part s1 s2 pf) -> Part s1 s2 (pf.i))
               (\(Part s1 s2 pf) -> Part s1 s2 (pf.from i))

-- It is not clear that we can create a part' because this witnesses a subset
-- relation on labels, which seems difficult to abstract

-- Composition -----------------------------------

-- A naïve attempt at implementing Comp is
--
-- data Comp f g l where
--   Comp :: f l1 -> M.Map l1 (g l2) -> ((l1,l2) <-> l) -> Comp f g l
--
-- However, this isn't right: we should be able to have a different
-- type l2 in each g-structure.  I.e. l2 should actually be indexed
-- on l1.  Note this isn't just an infelicity, we really can't use
-- this to implement comp: the typechecker will complain that it
-- can't prove all the l2 types stored in the Sp' structures are the
-- same.
--
-- Of course, we could use the above to implement
--
--   comp :: Sp f l1 (Sp g l2 a) -> Sp (Comp f g) (l1,l2) a
--
-- but this is wrong for the same reason.
--
-- Instead, we really want something like (as a pseudo-dependent-type):
--
--   f l1 -> (m : M.Map l1 (Sigma l2::*. g l2)) -> (Sum (map pi1 (elems m)) <-> l) -> Comp f g l
--
-- which we can encode in Haskell as follows:

data Comp f g l where
  Comp :: Eq l1
       => f l1
       -> LProxy (Size l1) ls
       -> V.HVec (Size l1) (Map g ls)
       -> (Sum ls <-> l)
       -> Comp f g l

instance BFunctor f => BFunctor (Comp f g) where
  bmap i = iso (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.i))
               (\(Comp fl lp gs pf) -> Comp fl lp gs (pf.from i))

-- compJ and compJ' are like generalized versions of 'join'.

-- compJ is a restricted form of composition where the substructures
-- are constrained to all have the same label type.
compJ :: forall f l1 g l2 a. (Eq l1, Finite l1) => Sp f l1 (Sp g l2 a) -> Sp (Comp f g) (l1,l2) a
compJ (Struct fSh es)
    = case mapRep l1Size (Proxy :: Proxy g) (Proxy :: Proxy l2) of
        Refl ->
          Struct (Comp fSh (lpRep l1Size (Proxy :: Proxy l2)) gShps' pf)
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
compJ' (Struct fSh es)
  = case unzipSpSp' es of
      UZSS ls gShps gElts ->
        SpEx (Struct
               (Comp fSh ls gShps id)
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

-- Functor composition ---------------------------

-- XXX todo

-- Cardinality restriction -----------------------

data OfSize :: Nat -> (* -> *) -> * -> * where
  OfSize :: SNat n -> (Fin n <-> l) -> f l -> OfSize n f l

instance BFunctor f => BFunctor (OfSize n f) where
  bmap i = iso (\(OfSize n eq f) -> OfSize n (eq.i) (view (bmap i) f))
               (\(OfSize n eq f) -> OfSize n (eq.from i) (view (bmap (from i)) f))

sizedSh :: forall f l. Finite l => Shape f l -> Shape (OfSize (Size l) f) l
sizedSh sh = OfSize (size (Proxy :: Proxy l)) finite sh

sized :: Finite l => Sp f l a -> Sp (OfSize (Size l) f) l a
sized (Struct s es) = Struct (sizedSh s) es

-- List ------------------------------------------

-- It turns out we don't need all that complicated type-level
-- machinery to do recursive labelled structures.  We can just embed
-- the recursion within Haskell by defining recursive shapes directly.
-- Here's an example.

newtype L l = L { unL :: (One + X * L) l }

isoL :: Iso (L l) (L l') ((One + X*L) l) ((One + X*L) l')
isoL = iso unL L

instance BFunctor L where
  bmap g = liftIso isoL isoL (bmap g)

-- Some introduction forms for lists, and an example of converting a
-- Haskell list to a Sp' L.  Ideally all of this would be generically
-- derivable.

listSh :: Finite l => Shape (One + X*L) l -> Shape L l
listSh = view (from isoL)

list :: Finite l => Sp (One + X*L) l a -> Sp L l a
list = reshape (view (from isoL))

nil :: Sp L (Fin Z) a
nil = list $ inl one

cons :: (Eq l', Finite l') => a -> Sp L l' a -> Sp L (Either (Fin (S Z)) l') a
cons a (Struct shp es) = Struct (listSh (inrSh (prodSh xSh shp))) (V.VCons a es)

fromList :: [a] -> Sp' L a
fromList [] = SpEx nil
fromList (a:as) =
  case fromList as of
    SpEx s -> SpEx (cons a s)

elimList :: r -> (a -> r -> r) -> Elim L a r
elimList r f = mapElimShape (view isoL)
             $ elimSum
                 (elimOne r)
                 (elimProd . elimX $ \a -> fmap (f a) (elimList r f))

------------------------------------------------------------
--  Eliminators for labelled structures

-- An eliminator for labelled structures should be able to look at the
-- labelling.  However, it should not actually care about the labels
-- that is, it should be indifferent to relabeling.  Fortunately, we
-- can actually enforce this in Haskell via parametricity.  We specify
-- that an eliminator must work for *any* label type which is an
-- instance of Eq.  (If we use Ord instead of Eq, we get eliminators
-- for L-species instead; if we use no constraint at all, Elim f a b
-- would be isomorphic to (f a -> b), that is, a usual eliminator for
-- (non-labeled) f-structures.)
--
-- Note that the difference between Elim f a b and (f a -> b) really
-- only matters for structures with sharing, e.g. cartesian product.

newtype Elim f a r = Elim (forall l. Eq l => Shape f l -> (l -> a) -> r)
  deriving Functor

-- Elim is a covariant functor in its final argument (witnessed by the
-- Functor instance) and contravariant in its first two, witnessed by
-- mapElimSrc and mapElimShape.

mapElimSrc :: (b -> a) -> Elim f a r -> Elim f b r
mapElimSrc f (Elim el) = Elim $ \s m -> el s (f . m)

mapElimShape :: (forall l. g l -> f l) -> Elim f a r -> Elim g a r
mapElimShape q (Elim el) = Elim $ \s m -> el (q s) m

-- Running eliminators

elim :: (Finite l, Eq l) => Elim f a b -> Sp f l a -> b
elim (Elim el) (Struct shp es) = el shp (V.vIndex es . view (from finite))

elim' :: Elim f a b -> Sp' f a -> b
elim' el (SpEx s) = elim el s

-- Some combinators for building eliminators

elimZero :: Elim Zero a r
elimZero = Elim (\z _ -> absurdZ z)

elimOne :: r -> Elim One a r
elimOne r = Elim (\_ _ -> r)
  -- arguably we should force the shape + proof contained therein

elimX :: (a -> r) -> Elim X a r
elimX f = Elim (\(X i) m -> f (m (view i FZ)))

elimSum :: Elim f a r -> Elim g a r -> Elim (f+g) a r
elimSum (Elim f) (Elim g) = Elim $ \shp m ->
  case shp of
    Inl fShp -> f fShp m
    Inr gShp -> g gShp m

elimProd :: Elim f a (Elim g a r) -> Elim (f*g) a r
elimProd (Elim f) = Elim $ \(Prod fShp gShp pf) m ->
  let mEither  = m . view pf
      (mf, mg) = (mEither . Left, mEither . Right)
  in
    case f fShp mf of
      Elim g -> g gShp mg

{-
-- XXX finish me!!  I know exactly how this is "supposed" to work but
haven't yet figured out how to convince the Haskell typechecker.

elimComp :: Elim f x r -> Elim g a x -> Elim (Comp f g) a r
elimComp (Elim ef) (Elim eg) = Elim $ \(Shape (Comp fl1 lp gs pf)) m ->
  let mSum = m . view pf
      -- mSum :: Sum ls -> a
  in
      ef (Shape fl1) (\l1 -> eg (Shape (undefined {- gs ! l1 -})) (mSum . undefined))
-}

------------------------------------------------------------
--  Generically deriving labelled structures

------------------------------------------------------------
--  Representable etc.

-- canonicalize :: forall l f a. (Finite l, Finite (Key f), Keyed f)
--              => Sp f l a -> (Sp E (Key f) a, l <-> Key f)
-- canonicalize (Struct (Shape fl) e)
--   = (Struct eSh (V.shuffle szL szK shuf e), i)
--   where
--     szL :: SNat (Size l)
--     szL = size Proxy
--     szK :: SNat (Size (Key f))
--     szK = size Proxy
--     i :: l <-> Key f
--     i    = iso undefined undefined
--     shuf :: Fin (Size (Key f)) -> Fin (Size l)
--     shuf = view shufIso
--     shufIso :: Fin (Size (Key f)) <-> Fin (Size l)
--     shufIso = finite . from i . from finite
