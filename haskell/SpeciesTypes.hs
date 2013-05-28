{-# LANGUAGE DeriveFunctor   #-}
{-# LANGUAGE EmptyDataDecls  #-}
{-# LANGUAGE GADTs           #-}
{-# LANGUAGE Rank2Types      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators   #-}

module SpeciesTypes where

import           BFunctor
import           Control.Lens hiding (cons)
import           Data.Void
import qualified Map          as M
import qualified Set          as S

------------------------------------------------------------
--  Labelled shapes and data structures

-- A labelled shape is a shape full of labels, along with a cached
-- (finite) size for convenience.
data Shape f l = Shape { _shapeSize :: Int, _shapeVal :: f l }

-- A species is a labelled shape paired with a map from labels to data
-- values.
data Sp f l a = Struct { _shape :: Shape f l, _elts :: M.Map l a }

makeLenses ''Shape
makeLenses ''Sp

------------------------------------------------------------
--  Relabelling/functoriality

-- Shapes are B-functors, i.e. they can be relabelled.
instance (BFunctor f) => BFunctor (Shape f) where
  bmap i = liftIso shapeVal shapeVal (bmap i)

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
--  Shape functors

-- Zero ------------------------------------------

data Zero l
  deriving Functor

instance BFunctor Zero

-- One -------------------------------------------

data One l = One (Void <-> l)

instance BFunctor One where
  bmap i = iso (\(One vl ) -> One (vl .i))
               (\(One vl') -> One (vl'.from i))

-- X ---------------------------------------------

data X l = X (() <-> l)

instance BFunctor X where
  bmap i = iso (\(X ul ) -> X (ul .i))
               (\(X ul') -> X (ul'.from i))

-- E ---------------------------------------------

data E l = E { _getE :: S.Set l }

makeLenses ''E

instance BFunctor E where
  bmap i = liftIso getE getE (bmap i)

-- Sum -------------------------------------------

infixl 6 +
data (f + g) l = Inl (f l)
               | Inr (g l)
  deriving Functor

instance (BFunctor f, BFunctor g) => BFunctor (f + g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g) => (l <-> l') -> (f + g) l -> (f + g) l'
      applyIso i (Inl f) = Inl (view (bmap i) f)
      applyIso i (Inr g) = Inr (view (bmap i) g)

-- parallel sum? ---------------------------------

-- No idea whether this is useful for anything but it seems to be
-- suggested by parallels with linear logic.  It's dual to product
-- just as Cartesian product is dual to sum.  It's pretty weird.

data (f +? g) l where
  ParSum :: (Either (f l1) (g l2)) -> (Either l1 l2 <-> l) -> (f +? g) l

instance (BFunctor f, BFunctor g) => BFunctor (f +? g) where
  bmap i = iso (\(ParSum e pf) -> ParSum e (pf.i))
               (\(ParSum e pf) -> ParSum e (pf.from i))

-- Product ---------------------------------------

infixl 7 *
data (f * g) l where
  Prod :: f l1 -> g l2 -> (Either l1 l2 <-> l) -> (f * g) l

instance (BFunctor f, BFunctor g) => BFunctor (f * g) where
  bmap i = iso (\(Prod f g pf) -> Prod f g (pf.i))
               (\(Prod f g pf) -> Prod f g (pf.from i))

-- Cartesian product -----------------------------

data (f # g) l where
  CProd :: f l -> g l -> (f # g) l

instance (BFunctor f, BFunctor g) => BFunctor (f # g) where
  bmap i = iso (applyIso i) (applyIso (from i))
    where
      applyIso :: (BFunctor f, BFunctor g) => (l <-> l') -> (f # g) l -> (f # g) l'
      applyIso i (CProd f g) = CProd (view (bmap i) f) (view (bmap i) g)

-- Differentiation -------------------------------

data D f l where
  D :: f l1 -> (l1 <-> Maybe l) -> D f l

instance BFunctor f => BFunctor (D f) where
  bmap i = iso (\(D f pf) -> D f (pf.iMaybe i))
               (\(D f pf) -> D f (pf.iMaybe (from i)))

iMaybe :: (a <-> b) -> (Maybe a <-> Maybe b)
iMaybe i = liftIso _Just _Just i

-- Pointing --------------------------------------

data P f l where
  P :: l -> f l -> P f l

instance BFunctor f => BFunctor (P f) where
  bmap i = iso (\(P l f) -> P (view i l) (view (bmap i) f))
               (\(P l f) -> P (view (from i) l) (view (bmap (from i)) f))

-- Composition -----------------------------------

-- XXX todo

-- Functor composition ---------------------------

-- XXX todo

-- Cardinality restriction -----------------------

-- XXX todo

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

nil :: Sp L Void a
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
--  Introduction forms for labelled structures

one :: Sp One Void a
one = Struct (Shape 0 (One id)) M.empty

x :: a -> Sp X () a
x a = Struct (Shape 1 (X id)) (M.singleton () a)

inl :: Sp f l a -> Sp (f + g) l a
inl (Struct (Shape n shp) es) = Struct (Shape n (Inl shp)) es

inr :: Sp g l a -> Sp (f + g) l a
inr (Struct (Shape n shp) es) = Struct (Shape n (Inr shp)) es

-- XXX finish

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

------------------------------------------------------------
--  Generically deriving labelled structures
