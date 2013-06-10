{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module ArithIsos where

import Control.Lens
import Finite
import Nat

------------------------------------------------------------
-- Some arithmetic isomorphisms

zeroPL :: Either (Fin Z) a <-> a
zeroPL = iso (either absurd id) Right

zeroPR :: Either a (Fin Z) <-> a
zeroPR = commP . zeroPL

commP :: Either a b <-> Either b a
commP = iso swap swap
        where swap (Left x)  = Right x
              swap (Right y) = Left y

zeroTL :: (Fin Z, a) <-> Fin Z
zeroTL = iso (absurd . fst) absurd

zeroTR :: (a, Fin Z) <-> Fin Z
zeroTR = commT . zeroTL

oneTL :: ((), a) <-> a
oneTL = iso snd ((,) ())

oneTR :: (a, ()) <-> a
oneTR = commT . oneTL

commT :: (a,b) <-> (b,a)
commT = iso swap swap
        where swap (a,b) = (b,a)

distribR :: (Either a b, c) <-> Either (a,c) (b,c)
distribR = iso distribR1 distribR2
  where
    distribR1 (Left a, c)   = Left (a,c)
    distribR1 (Right b, c)  = Right (b,c)
    distribR2 (Left (a,c))  = (Left a, c)
    distribR2 (Right (b,c)) = (Right b, c)

succFin :: Either () (Fin m) <-> Fin (S m)
succFin = iso succFin1 succFin2
  where
    succFin1 (Left ()) = FZ
    succFin1 (Right f) = FS f

    succFin2 :: Fin (S m) -> Either () (Fin m)
    succFin2 FZ        = Left ()
    succFin2 (FS f)    = Right f

assocLP :: Either b1 (Either b2 b3) <-> Either (Either b1 b2) b3
assocLP = iso shuffleRight shuffleLeft
          where
            shuffleRight (Left x)   = Left (Left x)
            shuffleRight (Right (Left x)) = Left (Right x)
            shuffleRight (Right (Right x)) = Right x

            shuffleLeft (Left (Left x)) = Left x
            shuffleLeft (Left (Right x)) = Right (Left x)
            shuffleLeft (Right x) = Right (Right x)

assocLT :: (b1,(b2,b3)) <-> ((b1,b2),b3)
assocLT = iso shuffleRight shuffleLeft
          where
            shuffleRight (a,(b,c)) = ((a,b),c)
            shuffleLeft ((a,b),c) = (a,(b,c))
