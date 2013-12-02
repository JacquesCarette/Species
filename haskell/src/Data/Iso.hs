{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeOperators        #-}

-- | Natural transformations, isomorphisms, and partial isomorphisms.
module Data.Iso
    ( -- * Isomorphisms and natural transformations

     type (<->), type (≅), liftIso, type (-->), type (<-->)

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

-- XXX comment me
type (≅) a b = AnIso' a b

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
