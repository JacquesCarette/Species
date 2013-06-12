module FinPf

weaken' : {m,k : Nat} -> Fin m -> Fin (plus k m)
weaken'         fO     =? fO
weaken' {k = q} (fS f) =  let ih = (weaken' {k=S q} f)
	     	       	  in  ?weakenS

Fin' : Nat -> Type
Fin' m = (n : Nat ** LT n m)

toFin' : Fin m -> Fin' m
toFin' fO     = (O ** lteSucc lteZero)
toFin' (fS f) with (toFin' f)
  | (n ** pf) = (S n ** lteSucc pf)

toFin : Fin' m -> Fin m
toFin (Z ** lteSucc _)      = fO
toFin ((S n) ** lteSucc pf) = fS (toFin (n ** pf))

fin'Pair : Fin' m -> Fin' n -> Fin' (mult m n)
fin'Pair {m=S m'} (i ** iLTm) (j ** jLTn) = ((i*(S m') + j) ** ?ltPf)

-- finPair : Fin m -> Fin n -> Fin (mult m n)
-- finPair {m=S O} fO fn        ?= fn
-- finPair {m=S m'} (fS fm') fn  = let ih = finPair fm' fn in ?finPair_S

---------- Proofs ----------

FinPf.weakenS = proof {
  intros;
  rewrite plusSuccRightSucc q k;
  trivial;
}

FinPf.fO = proof {
  intros;
  rewrite (plusSuccRightSucc k k1);
  exact fO;
}

