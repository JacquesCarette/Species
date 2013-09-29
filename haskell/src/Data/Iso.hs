{-# LANGUAGE Rank2Types           #-}
{-# LANGUAGE TypeOperators        #-}

-- | Natural transformations and isomorphisms.
module Data.Iso
    ( -- * Isomorphisms and natural transformations

     type (<->), liftIso, type (-->), type (<-->)

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

------------------------------------------------------------
--  Natural transformations

-- | Natural transformations between two shapes.
type (-->) f g = forall l. (Eq l) => f l -> g l

