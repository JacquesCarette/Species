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

module SpeciesTypes where

import           BFunctor
import           Control.Lens hiding (cons)
import           Data.Functor ((<$>))
import           Data.Maybe   (fromJust)
import           Nat
import qualified Map          as M
import qualified Set          as S

------------------------------------------------------------
--  Labelled shapes and data structures

-- A labelled shape is a shape full of labels, along with a proof that
-- the label type has a given (finite) size.
data Shape :: (* -> *) -> * -> * where
  Shape { _shapeSize :: SNat n
        , _finPf     :: Fin n <-> l
        , _shapeVal  :: f l
        }
    :: Shape f l

shapeSize :: Shape f l -> Int
shapeSize (Shape n _ _) = snatToInt n

shapeVal :: Lens (Shape f l) (Shape g l) (f l) (g l)
shapeVal g (Shape sz pf s) = (\s' -> Shape sz pf s') <$> g s

-- A species is a labelled shape paired with a map from labels to data
-- values.
data Sp f l a = Struct { _shape :: Shape f l, _elts :: M.Map l a }

makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

-- Shapes are B-functors, i.e. they can be relabelled.
instance (BFunctor f) => BFunctor (Shape f) where
  bmap i = iso (\(Shape sz pf v) -> Shape sz (pf.i) (view (bmap i) v))
               (\(Shape sz pf v) -> Shape sz (pf.from i) (view (bmap (from i)) v))

relabelShape' :: BFunctor f => (l1 <-> l2) -> (Shape f l1 <-> Shape f l2)
relabelShape' = bmap

relabelShape :: BFunctor f => (l1 <-> l2) -> Shape f l1 -> Shape f l2
relabelShape = view . bmap

-- Species structures can also be relabelled.
relabel' :: BFunctor f => (l1 <-> l2) -> (Sp f l1 a <-> Sp f l2 a)
relabel' i =
  iso (\(Struct shp es) -> Struct (relabelShape i shp) (M.relabel i es))
      (\(Struct shp es) -> Struct (relabelShape (from i) shp) (M.relabel (from i) es))

relabel :: BFunctor f => (l1 <-> l2) -> Sp f l1 a -> Sp f l2 a
relabel = view . relabel'

instance Functor (Sp f l) where
  fmap = over (elts . mapped)

------------------------------------------------------------
--  Reshaping

reshapeShape' :: (f <--> g) -> (Shape f l <-> Shape g l)
reshapeShape' i = liftIso shapeVal shapeVal i

reshapeShape :: (f <--> g) -> Shape f l -> Shape g l
reshapeShape = view . reshapeShape'

reshape' :: (f <--> g) -> (Sp f l a <-> Sp g l a)
reshape' i = liftIso shape shape (reshapeShape' i)

reshape :: (f <--> g) -> Sp f l a -> Sp g l a
reshape = view . reshape'

------------------------------------------------------------
--  Existentially labelled structures

-- We need to package up an Eq constraint on the labels, otherwise we
-- can't really do anything with them and we might as well just not
-- have them at all.

data Sp' f a where
  SpEx :: Eq l => Sp f l a -> Sp' f a

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

-- One -------------------------------------------

data One l = One (Fin Z <-> l)

instance BFunctor One where
  bmap i = iso (\(One vl ) -> One (vl .i))
               (\(One vl') -> One (vl'.from i))

oneSh :: Shape One (Fin Z)
oneSh = Shape SZ id (One id)

one :: Sp One (Fin Z) a
one = Struct oneSh M.empty

one' :: Sp' One a
one' = SpEx one

-- X ---------------------------------------------

data X l = X (Fin (S Z) <-> l)

instance BFunctor X where
  bmap i = iso (\(X ul ) -> X (ul .i))
               (\(X ul') -> X (ul'.from i))

xSh :: Shape X (Fin (S Z))
xSh = Shape (SS SZ) id (X id)

x :: a -> Sp X (Fin (S Z)) a
x a = Struct xSh (M.singleton FZ a)

x' :: a -> Sp' X a
x' = SpEx . x

-- E ---------------------------------------------

data E n l = E { _getE :: S.Set n l }

makeLenses ''E

instance BFunctor (E n) where
  bmap i = liftIso getE getE (bmap i)

-- XXX TODO, fix me!
--   - index Map by size
--   - should all shape functors be indexed by size??

-- eSh :: S.Set n l -> Shape (E n) l
-- eSh ls = Shape (S.size ls) (E ls)

-- e :: Eq l => M.Map l a -> Sp E l a
-- e m = Struct (eSh (M.keys m)) m

-- e' :: [a] -> Sp' E a
-- e' [] = SpEx (Struct (eSh (S.empty :: S.Set (Fin Z))) M.empty)
-- e' (a:as) = case e' as of
--               SpEx (Struct (Shape n (E ls)) es) ->
--                 SpEx (Struct (Shape (n+1) (E (S.insert Nothing (S.mapInj Just ls))))
--                              (M.insert Nothing a (M.mapLabels Just es))
--                      )

-- Sum -------------------------------------------

infixl 6 +
data (f + g) (l :: *) = Inl (f l)
                      | Inr (g l)
  deriving Functor

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g) => (l <-> l') -> (f + g) l -> (f + g) l'
      applyIso i (Inl f) = Inl (view (bmap i) f)
      applyIso i (Inr g) = Inr (view (bmap i) g)

inlSh :: Shape f l -> Shape (f + g) l
inlSh (Shape n shp) = Shape n (Inl shp)

inl :: Sp f l a -> Sp (f + g) l a
inl (Struct shp es) = Struct (inlSh shp) es

inl' :: Sp' f a -> Sp' (f + g) a
inl' (SpEx s) = SpEx (inl s)

inrSh :: Shape g l -> Shape (f + g) l
inrSh (Shape n shp) = Shape n (Inr shp)

inr :: Sp g l a -> Sp (f + g) l a
inr (Struct shp es) = Struct (inrSh shp) es

inr' :: Sp' g a -> Sp' (f + g) a
inr' (SpEx s) = SpEx (inr s)

-- parallel sum? ---------------------------------

-- No idea whether this is useful for anything but it seems to be
-- suggested by parallels with linear logic.  It's dual to product
-- just as Cartesian product is dual to sum.  It's pretty weird.

data (f +? g) l where
  ParSum :: (Either (f l1) (g l2)) -> (Either l1 l2 <-> l) -> (f +? g) l

instance (BFunctor f, BFunctor g) => BFunctor (f +? g) where
  bmap i = iso (\(ParSum e pf) -> ParSum e (pf.i))
               (\(ParSum e pf) -> ParSum e (pf.from i))

pInlSh :: Shape f l1 -> Shape (f +? g) (Either l1 l2)
pInlSh (Shape n f) = Shape n (ParSum (Left f) id)

pInl :: Sp f l1 a -> Sp (f +? g) (Either l1 l2) a
pInl (Struct s es) = Struct (pInlSh s) (M.mapLabels Left es)

-- This doesn't typecheck because l2 is completely ambiguous.
-- Fundamentally this is because ParSum is weird.
--
-- pInl' :: Sp' f a -> Sp' (f +? g) a
-- pInl' (SpEx s) = SpEx (pInl s)

-- Product ---------------------------------------

infixl 7 *
data (f * g) l where
  Prod :: f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap i = iso (\(Prod f g pf) -> Prod f g (pf.i))
               (\(Prod f g pf) -> Prod f g (pf.from i))

prodSh :: Shape f l1 -> Shape g l2 -> Shape (f * g) (Either l1 l2)
prodSh (Shape m f) (Shape n g) = Shape (m+n) (Prod f g id)

prod :: Sp f l1 a -> Sp g l2 a -> Sp (f * g) (Either l1 l2) a
prod (Struct sf esf) (Struct sg esg) = Struct (prodSh sf sg)
                                              (M.mapLabels Left esf `M.union` M.mapLabels Right esg)

prod' :: Sp' f a -> Sp' g a -> Sp' (f * g) a
prod' (SpEx f) (SpEx g) = SpEx (prod f g)

-- Cartesian product -----------------------------

data (f # g) l where
  CProd :: f l -> g l -> (f # g) l

instance (BFunctor f, BFunctor g) => BFunctor (f # g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g) => (l <-> l') -> (f # g) l -> (f # g) l'
      applyIso i (CProd f g) = CProd (view (bmap i) f) (view (bmap i) g)

cprodSh :: Shape f l -> Shape g l -> Shape (f # g) l
cprodSh (Shape m f) (Shape _ g) = Shape m (CProd f g)
  -- XXX what to do about cached sizes here? dynamically throw an
  -- error if they don't match... or just assume that they do match?

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
dSh (Shape n f) = Shape (n-1) (D f id)

d :: Sp f (Maybe l) a -> Sp (D f) l a
d (Struct s es) = Struct (dSh s) (M.remap id es)

-- No d' operation since it really does depend on the labels

-- Pointing --------------------------------------

data P f l where
  P :: l -> f l -> P f l

instance BFunctor f => BFunctor (P f) where
  bmap i = iso (\(P l f) -> P (view i l) (view (bmap i) f))
               (\(P l f) -> P (view (from i) l) (view (bmap (from i)) f))

pSh :: l -> Shape f l -> Shape (P f) l
pSh l (Shape n f) = Shape n (P l f)

p :: l -> Sp f l a -> Sp (P f) l a
p l (Struct s es) = Struct (pSh l s) es

-- No p' operation---it again depends on the labels

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
  Comp :: f l1
       -> (l1 <-> Fin n)
       -> Proxy ls
       -> Apply g n ls
       -> (Sum ls <-> l)
       -> Comp f g l

data Proxy a = Proxy

type family Apply (g :: * -> *) (n :: Nat) (ls :: [*]) :: *
type instance Apply g Z     '[]       = ()
type instance Apply g (S n) (l ': ls) = (g l, Apply g n ls)

type family Sum (ls :: [*]) :: *
type instance Sum '[]       = Fin Z
type instance Sum (l ': ls) = Either l (Sum ls)

data Shape' :: (* -> *) -> * where
  Shape' :: Shape f l -> Shape' f

data LProxy' where
  LProxy' :: Proxy (a :: [*]) -> LProxy'

-- ugh agh ick.  Extract the existentially quantified label types from
-- a list of shapes and put them in an existentially quantified
-- type-level list.  Oh how I dearly wish I did not have to choose
-- between practicality and actual dependent types.
getLabelTypes :: [Shape' g] -> LProxy'
getLabelTypes [] = LProxy' (Proxy :: Proxy '[])
getLabelTypes (Shape' (Shape _ (_ :: g l)) : ss) =
  case getLabelTypes ss of
    LProxy' (Proxy :: Proxy ls) -> LProxy' (Proxy :: Proxy (l ': ls))

-- argh, probably need the above to keep around more information about the length?

compSh :: IsFinite l => Sp f l (Shape' g) -> Shape' (Comp f g)
compSh (Struct (Shape _ fl) es) =
    case (finite, getLabelTypes shps) of
      (Finite finPf, LProxy' prox) -> Shape' (Shape n' (Comp fl finPf prox undefined id))
  where
    shps                              = M.elems es
    ns                                = map getShapeSize shps
    getShapeSize (Shape' (Shape s _)) = s
    n'                                = sum ns

comp :: IsFinite l => Sp f l (Sp' g a) -> Sp' (Comp f g) a
comp = undefined

-- Functor composition ---------------------------

-- XXX todo

-- Cardinality restriction -----------------------

-- data OfSize :: Nat -> (* -> *) -> * -> * where
--   OfSize :: SNat n -> (Fin n <-> l) -> f l -> OfSize n f l

-- instance BFunctor f => BFunctor (OfSize n f) where
--   bmap i = iso (\(OfSize n pf f) -> OfSize n (pf.i) (view (bmap i) f))
--                (\(OfSize n pf f) -> OfSize n (pf.from i) (view (bmap (from i)) f))

-- ofSizeSh :: SNat n -> (Fin n <-> l) -> Shape f l -> OfSize n f l
-- ofSizeSh n pf (Shape m

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

list :: Sp (One + X*L) l a -> Sp L l a
list = reshape (from isoL)

nil :: Sp L (Fin Z) a
nil = list $ inl one

cons :: a -> Sp L l' a -> Sp L (Either () l') a
cons a (Struct (Shape n shp) es) = Struct shp' es'
  where
    shp' = Shape (n+1) (L (Inr (Prod (X id) shp id)))
    es'  = M.insert (Left ()) a (M.mapLabels Right es)

toList :: [a] -> Sp' L a
toList [] = SpEx nil
toList (x:xs) =
  case toList xs of
    SpEx s -> SpEx (cons x s)

------------------------------------------------------------
--  Eliminators for labelled structures

-- An eliminator for labelled structures should be able to look at the labelling.
-- XXX but should be restricted to not care about the labels -- parametricity!
-- XXX need Eq by default.  Ord gives us L-species.  No constraint is isomorphic to (f a -> b).
-- XXX this only really matters for e.g. cartesian product.
newtype Elim f a b = Elim (forall l. Eq l => Shape f l -> M.Map l a -> b)

elim :: Eq l => Elim f a b -> Sp f l a -> b
elim (Elim el) (Struct s e) = el s e

elim' :: Elim f a b -> Sp' f a -> b
elim' el (SpEx s) = elim el s

-- Some combinators for building eliminators

elimZero :: Elim Zero a r
elimZero = undefined

elimOne :: r -> Elim One a r
elimOne r = Elim (\_ _ -> r)   -- arguably we should force the shape + proof contained therein

elimX :: (a -> r) -> Elim X a r
elimX f = Elim (\(Shape _ (X i)) m -> f (fromJust (M.lookup (view i ()) m)))

elimSum :: Elim f a r -> Elim g a r -> Elim (f+g) a r
elimSum ef eg = undefined

elimProd :: Elim f a (Elim g a r) -> Elim (f*g) a r
elimProd e = undefined

------------------------------------------------------------
--  Generically deriving labelled structures
