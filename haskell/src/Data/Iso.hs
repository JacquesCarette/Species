{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeOperators        #-}

-- | Natural transformations, isomorphisms, and partial isomorphisms.
module Data.Iso
    ( -- * Isomorphisms and natural transformations

     type (<->), liftIso, type (<-?>), type (-->), type (<-->)

    , subtractIso
    )
    where

import           Control.Lens

------------------------------------------------------------
--  Isomorphisms

-- | The type @a \<-\> b@ represents isomorphisms between @a@ and @b@.
--
--   * To construct one, you can pass a pair of inverse functions to
--     'iso', or use 'liftIso' as described below.
--
--   * To invert an isomorphism, use @'from' :: (a \<-\> b) -> (b \<-\> a)@.
--
--   * To compose two isomorphisms, use the normal function
--     composition operator '.' (though note it works \"backwards\",
--     /i.e./ @(.) :: (a \<-\> b) -> (b \<-\> c) -> (a \<-\> c)@.
--
--   * To turn an isomorphism into a function, use @'view' :: (a \<-\>
--     b) -> (a -> b)@.
type (<->) a b = Iso' a b

-- | The type @a \<-?\> b@ represents /partial isomorphisms/ between
--   @a@ and @b@.  In particular, every value of type @b@ has a
--   corresponding value of type @a@, but the converse is not
--   necessarily true: some values of @a@ may have no corresponding
--   @b@ value.  Intuitively, @a \<-?\> b@ may be thought of as
--   providing computational evidence witnessing the fact that "@a@ is
--   a superset of @b@".
--
--   * To construct one, use @prism' :: (b -\> a) -\> (a -\> Maybe b)
--     -\> (a \<-?\> b)@, being careful to satisfy the laws: for @prism'
--     f g@ we should have (1) @g . f === Just@, and (2) if @g a = Just
--     b@ then @f b = a@.
--
--   * Any isomorphism may be used directly as a partial isomorphism.
--
--   * To turn a partial isomorphism into a function in the forward
--     (partial) direction, use 'preview'.
--
--   * To turn a partial isomorphism into a function in the backwards
--     (total) direction, use 'review'.
--
--   * Unlike with isomorphisms, it does not make sense to invert
--     partial isomorphisms, since they have an inherent directionality.
--
--   * To compose two partial isomorphisms (or an isomorphism and a
--     partial isomorphism), use the normal function composition
--     operator '.' (though note it works \"backwards\", /i.e./ @(.)
--     :: (a \<-?\> b) -> (b \<-?\> c) -> (a \<-?\> c)@.
type (<-?>) a b = Prism' a b

-- | Higher-order isomorphisms, /i.e./ natural isomorphisms, between
--   two shapes.
type (<-->) f g = forall l. Eq l => f l <-> g l

-- | Lift an isomorphism on a particular field to an isomorphism of an
--   entire structure.  Unfortunately, the field must be passed twice
--   (this is simply due to a quirk of the way @lens@ is encoded).  For example,
--
--   > liftIso _1 _1 :: (a <-> b) -> ((a,c) <-> (b,c))
liftIso :: Setter s t a b -> Setter t s b a -> (a <-> b) -> (s <-> t)
liftIso l1 l2 ab = withIso ab $ \f g -> iso (l1 %~ f) (l2 %~ g)

-- | A simplified variant of the Garsia-Milne involution principle.
--   If we have an iso (A <-> B) and an iso (A+C <-> B+D), then we can
--   \"subtract" the first from the second to obtain an explicit iso
--   (C <-> D).
--
--   XXX draw a picture to illustrate how this works
subtractIso :: (a <-> b) -> (Either a c <-> Either b d) -> (c <-> d)
subtractIso ab e = iso (iter ab e . Right) (iter (from ab) (from e) . Right)
  where
    iter :: (a <-> b) -> (Either a c <-> Either b d) -> Either a c -> d
    iter ab e eac
      = case view e eac of
          Right d -> d
          Left  b -> iter ab e (Left (view (from ab) b))

------------------------------------------------------------
--  Natural transformations

-- | Natural transformations between two shapes.
type (-->) f g = forall l. (Eq l) => f l -> g l

