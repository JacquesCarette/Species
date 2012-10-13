{-# OPTIONS --type-in-type #-}

module Species where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Product

open import Data.Nat
open import Relation.Binary.PropositionalEquality as P
open import Data.Fin
open import Data.Vec

open import Relation.Binary

open import Function.Inverse hiding ( _∘_ )
open import Function.Bijection hiding ( _∘_ )

import Level

Species = Set -> Set

{-
-- A species is a mapping from sets of labels to sets of structures,
-- which lifts bijections functorially.
record Species (F : Set -> Set) : Set where
  field
    functorial : ∀ {U T} 
              -> (Bijection (P.setoid U) (P.setoid T)) 
              -> (Bijection (P.setoid (F U)) (P.setoid (F T)))
-}

-- The zero species has no inhabitants
data ZERO : Species where

-- The one species has a single structure at any empty label set,
-- i.e. any label set isomorphic to ⊥.
data ONE (U : Set) : Set where 
  One : (U ↔ ⊥) -> ONE U

-- The X species has a single structure at any single-element label
-- set, i.e. any label set isomorphic to ⊤. The X structure itself
-- simply consists of the single label.
data X (U : Set) : Set where
  Id : (U ↔ ⊤) -> U -> X U

-- Addition of species is just disjoint union.
data _⊕_ (F G : Species) (U : Set) : Set where
  in₁ : F U -> (F ⊕ G) U
  in₂ : G U -> (F ⊕ G) U

-- Species product is pairing where the labels are partitioned between
-- the two substructures.  That is, an ((F ⊗ G) U)-structure is a pair
-- of an (F U₁)- and a (G U₂)-structure, where U is (isomorphic to)
-- the disjoint union (U₁ ⊎ U₂).
data _⊗_ (F G : Species) (U : Set) : Set where
  pair : {U₁ U₂ : Set} -> (U ↔ (U₁ ⊎ U₂)) -> F U₁ -> G U₂ -> (F ⊗ G) U

-- Form the disjoint union of a vector of types.
tsum : {n : ℕ} -> Vec Set n -> Set
tsum = foldr (λ _ → Set) _⊎_ ⊥

-- Form the product of a vector of types.
tprod : {n : ℕ} -> Vec Set n -> Set
tprod = foldr (λ _ → Set) _×_ ⊤

-- Species composition: An ((F ∘ G) U)-structure is built by
-- partitioning U into subsets, creating a G-structure from each
-- subset, and an F-structure of the resulting G-structures.  In other
-- words, it is an F-structure of G-structures, but we only use each
-- label once.
data _∘_ (F G : Species) (U : Set) : Set where
  comp : {n : ℕ}            -- An ((F ∘ G) U)-structure consists of:
       -> (p : Vec Set n)   --   A length-n list of label sets, p
       -> (U ↔ tsum p)      --   ...which is a partition of U
       -> tprod (Data.Vec.map G p)  -- A G-structure on each of the sets
                                    --   in p
       -> F (Fin n)         --   An F-structure built from the list of
                            --   G-structures; we represent each
                            --   G-structure by its index
       -> (F ∘ G) U

---------------------------------------------------------------

Fin0-elim : {Whatever : Set} -> Fin 0 -> Whatever
Fin0-elim ()

Fin0-elim-cong : {Whatever : Set} -> {i j : Fin 0} → i ≡ j → Whatever
Fin0-elim-cong {_} {()}

⊥-elim-cong : {Whatever : Set} -> {i j : ⊥} → i ≡ j → Whatever
⊥-elim-cong {_} {()}

Fin0↔⊥ : Fin 0 ↔ ⊥
Fin0↔⊥ = 
  record 
  { to = record { _⟨$⟩_ = Fin0-elim; cong = Fin0-elim-cong}
  ; from = record { _⟨$⟩_ = ⊥-elim; cong = ⊥-elim-cong }
  ; inverse-of = record 
    { left-inverse-of = λ x → Fin0-elim x
    ; right-inverse-of = λ x → ⊥-elim x 
    } 
  }

Fin1-unique : (x : Fin 1) → zero ≡ x
Fin1-unique zero = refl
Fin1-unique (suc ())

⊤-unique : (x : ⊤) → tt ≡ x
⊤-unique tt = refl

Fin1↔⊤ : Fin 1 ↔ ⊤
Fin1↔⊤ = 
  record 
  { to   = record { _⟨$⟩_ = λ x → tt; cong = λ x → refl }
  ; from = record { _⟨$⟩_ = λ x → zero; cong = λ x → refl }
  ; inverse-of = record 
    { left-inverse-of = Fin1-unique
    ; right-inverse-of = ⊤-unique
    }
  }

X₁ : X (Fin 1)
X₁ = Id Fin1↔⊤ zero

Maybe : Species
Maybe = ONE ⊕ X

Nothing : Maybe (Fin 0)
Nothing = in₁ (One Fin0↔⊥)

Just : Maybe (Fin 1)
Just = in₂ X₁

Pair : Species
Pair = X ⊗ X

bij1 : Fin 2 -> Fin 1 ⊎ Fin 1
bij1 zero    = inj₁ zero
bij1 (suc _) = inj₂ zero

bij1-cong : {i j : Fin 2} -> i ≡ j -> bij1 i ≡ bij1 j
bij1-cong {zero}  {zero}   _  = refl
bij1-cong {zero}  {suc i}  ()
bij1-cong {suc i} {zero}   ()
bij1-cong {suc i} {suc i'} _  = refl

bij1-inv : Fin 1 ⊎ Fin 1 -> Fin 2
bij1-inv (inj₁ _) = zero
bij1-inv (inj₂ _) = suc zero

bij1-inv-cong : {i j : Fin 1 ⊎ Fin 1} -> i ≡ j -> bij1-inv i ≡ bij1-inv j
bij1-inv-cong {inj₁ _} {inj₁ _} _ = refl
bij1-inv-cong {inj₁ _} {inj₂ _} ()
bij1-inv-cong {inj₂ _} {inj₁ _} ()
bij1-inv-cong {inj₂ _} {inj₂ _} _ = refl

bij1-li : (x : Fin 2) → bij1-inv (bij1 x) ≡ x
bij1-li zero = refl
bij1-li (suc zero) = refl
bij1-li (suc (suc ()))

bij1-ri : (x : Fin 1 ⊎ Fin 1) → bij1 (bij1-inv x) ≡ x
bij1-ri (inj₁ zero) = refl
bij1-ri (inj₁ (suc ()))
bij1-ri (inj₂ zero) = refl
bij1-ri (inj₂ (suc ()))

pair1 : Pair (Fin 2)
pair1 = 
  pair 
    record 
    { to = record { _⟨$⟩_ = bij1; cong = bij1-cong}
    ; from = record { _⟨$⟩_ = bij1-inv; cong = bij1-inv-cong }
    ; inverse-of = record 
      { left-inverse-of = bij1-li
      ; right-inverse-of = bij1-ri 
      } 
    }         
    X₁
    X₁

MP : Species
MP = Maybe ∘ Pair

mp0 : MP ⊥
mp0 = comp [] Function.Inverse.id tt (in₁ (One Fin0↔⊥))

inj₁-cong : ∀ {U : Set} {x y : U} -> x ≡ y -> inj₁ x ≡ inj₁ y
inj₁-cong refl = refl

projL : ∀ {U : Set} -> U ⊎ ⊥ -> U
projL (inj₁ x) = x
projL (inj₂ ())

projL-cong : ∀ {U : Set} {i j : U ⊎ ⊥} → i ≡ j → projL i ≡ projL j
projL-cong refl = refl

inj₁-projL-id : ∀ {U : Set} -> (x : U ⊎ ⊥) -> inj₁ (projL x) ≡ x
inj₁-projL-id (inj₁ x) = refl
inj₁-projL-id (inj₂ ())

pf : Fin 2 ↔ (Fin 2 ⊎ ⊥)
pf = record 
  { to         = record { _⟨$⟩_ = inj₁;  cong = inj₁-cong }
  ; from       = record { _⟨$⟩_ = projL; cong = projL-cong }
  ; inverse-of = record 
    { left-inverse-of = λ _ -> refl
    ; right-inverse-of = inj₁-projL-id 
    } 
  }

mp1 : MP (Fin 2)
mp1 = comp (Fin 2 ∷ []) pf (pair1 , tt) (in₂ X₁)
