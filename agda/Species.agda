{-# OPTIONS --without-K #-}

open import HoTT
open import GCBP

module Species where

-- Fin -----------------------------------------------------

data Fin : ℕ → Set where
  fO : {n : ℕ} → Fin (S n)
  fS : {n : ℕ} → Fin n → Fin (S n)

fO-elim : ∀ {i} {A : Fin 0 → Type i} → (x : Fin 0) → A x
fO-elim ()

⊥≃Fin0 : ⊥ ≃ Fin 0
⊥≃Fin0 = equiv Empty-elim fO-elim fO-elim Empty-elim

Fin1=fO : (a : Fin 1) → fO == a
Fin1=fO fO = idp
Fin1=fO (fS ())

⊤≃Fin1 : ⊤ ≃ Fin 1
⊤≃Fin1 = equiv (cst fO) (cst unit) Fin1=fO (λ {unit → idp})

-- Codes for labels ----------------------------------------

-- We use a set of codes for "allowed" label types, to get around
-- problems with impredicativity.  The specific codes used are not
-- important; in principle we can add codes for as many things as we
-- like.  The important point is that we cannot use a set of species
-- structures as labels.

data Code : Set where
  CFin  : ℕ → Code
  CSum  : Code → Code → Code
  CProd : Code → Code → Code

⟦_⟧ : Code → Set
⟦ CFin n ⟧ = Fin n
⟦ CSum  c₁ c₂ ⟧ = Coprod ⟦ c₁ ⟧ ⟦ c₂ ⟧
⟦ CProd c₁ c₂ ⟧ = ⟦ c₁ ⟧ × ⟦ c₂ ⟧

-- We require the property that two distinct codes never map to the
-- same interpretation.  This would be straightforward but tedious to
-- prove by induction on codes; for now we simply postulate it as an
-- axiom.

-- postulate Codes-unique : (c₁ c₂ : Code) → (⟦ c₁ ⟧ == ⟦ c₂ ⟧) → (c₁ == c₂)

-- Actually, I thought I needed it but don't use it now.  Leaving it
-- here but commented out.

-- FinSet --------------------------------------------------

-- syntax Σ A (λ a → B) = Σ[ a ∈ A ] B

IsFinite : Code → Set
IsFinite A = Σ ℕ (λ n → Fin n ≃ ⟦ A ⟧)

FinSet : Set
FinSet = Σ Code IsFinite

CodeOf : FinSet → Code
CodeOf ( C , _ ) = C

-- \|
∣_∣ : FinSet → ℕ
∣ _ , (n , _) ∣ = n

-- \clL , \clR
⌊_⌋ : FinSet → Set
⌊ A , _ ⌋ = ⟦ A ⟧

FinPf : (L : FinSet) → (Fin ∣ L ∣ ≃ ⌊ L ⌋)
FinPf ( _ , (_ , p)) = p

⌈_⌉ : ℕ → FinSet
⌈ n ⌉ = CFin n , (n , ide (Fin n))

-- This is actually false: finite proofs may not match
-- lift-⌊⌋-equiv : ∀ {L₁ L₂ : FinSet} → (⌊ L₁ ⌋ ≃ ⌊ L₂ ⌋) → (L₁ == L₂)

FinSet-equiv→ : (L₁ L₂ : FinSet) → (L₁ == L₂) →
  Σ (⌊ L₁ ⌋ ≃ ⌊ L₂ ⌋) (λ p →
  Σ (∣ L₁ ∣ == ∣ L₂ ∣)  (λ q →
    (transport (λ S₁ → Fin ∣ L₂ ∣ ≃ S₁) (ua p)
       (transport (λ sz → Fin sz ≃ ⌊ L₁ ⌋) q (FinPf L₁)) == FinPf L₂)
  ))
FinSet-equiv→ (C₁ , (n₁ , f₁)) (C₂ , (n₂ , f₂)) L₁==L₂ = (coe-equiv (ap ⟦_⟧ (fst= L₁==L₂))) , ({!!} , {!!})


-- Species -------------------------------------------------

Species : Set₁
Species = FinSet → Set

relabel : ∀ {F : Species} {L₁ L₂ : FinSet} → (L₁ == L₂) → F L₁ → F L₂
relabel {F} = transport F

-- Species algebra -----------------------------------------

-- Zero --------------------------------

Zero : Species
Zero _ = ⊥

-- One ---------------------------------

One : Species
One L = ⊥ ≃ ⌊ L ⌋

one : One ⌈ 0 ⌉
one = ⊥≃Fin0

-- X -----------------------------------

X : Species
X L = ⊤ ≃ ⌊ L ⌋

x : X ⌈ 1 ⌉
x = ⊤≃Fin1

-- Sum ---------------------------------

_⊎_ : {i j : ULevel} → Set i → Set j → Set (lmax j i)
_⊎_ = Coprod
-- \u+

⊎-assocL : ∀ {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
⊎-assocL (inl x) = inl (inl x)
⊎-assocL (inr (inl x)) = inl (inr x)
⊎-assocL (inr (inr x)) = inr x

⊎-assocR : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
⊎-assocR (inl (inl x)) = inl x
⊎-assocR (inl (inr x)) = inr (inl x)
⊎-assocR (inr x) = inr (inr x)

⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = equiv ⊎-assocR ⊎-assocL ⊎-RL ⊎-LR
  where
    ⊎-RL : ∀ {A B C : Set} → (b : A ⊎ (B ⊎ C)) → ⊎-assocR (⊎-assocL b) == b
    ⊎-RL (inl x) = idp
    ⊎-RL (inr (inl x)) = idp
    ⊎-RL (inr (inr x)) = idp

    ⊎-LR : ∀ {A B C : Set} → (b : (A ⊎ B) ⊎ C) → ⊎-assocL (⊎-assocR b) == b
    ⊎-LR (inl (inl x)) = idp
    ⊎-LR (inl (inr x)) = idp
    ⊎-LR (inr x) = idp

⊎-idL : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊎-idL = equiv ⊎-projR inr (λ _ → idp) ⊎-inrProjR
  where
    ⊎-projR : ∀ {A : Set} → (⊥ ⊎ A) → A
    ⊎-projR (inl ())
    ⊎-projR (inr a) = a
    ⊎-inrProjR : ∀ {A : Set} → (a : ⊥ ⊎ A) → inr (⊎-projR a) == a
    ⊎-inrProjR (inl ())
    ⊎-inrProjR (inr x) = idp

⊎-idR : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊎-idR = equiv ⊎-projL inl (λ _ → idp) ⊎-inlProjL
  where
    ⊎-projL : ∀ {A : Set} → (A ⊎ ⊥) → A
    ⊎-projL (inl a) = a
    ⊎-projL (inr ())
    ⊎-inlProjL : ∀ {A : Set} → (a : A ⊎ ⊥) → inl (⊎-projL a) == a
    ⊎-inlProjL (inl x) = idp
    ⊎-inlProjL (inr ())

_⊞_ : Species → Species → Species
(F ⊞ G) L = F L ⊎ G L
-- \b+

⊞inl : ∀ {F G : Species} {L : FinSet} → F L → (F ⊞ G) L
⊞inl = inl

⊞inr : ∀ {F G : Species} {L : FinSet} → G L → (F ⊞ G) L
⊞inr = inr

⊞-assoc : ∀ {F G H : Species} → ((F ⊞ G) ⊞ H) == (F ⊞ (G ⊞ H))
⊞-assoc = λ= (λ _ → ua ⊎-assoc)

⊞-idL : ∀ {F : Species} → (Zero ⊞ F) == F
⊞-idL = λ= (λ _ → ua ⊎-idL)

⊞-idR : ∀ {F : Species} → (F ⊞ Zero) == F
⊞-idR = λ= (λ _ → ua ⊎-idR)

-- Product -----------------------------

-- \b.
_⊡_ : Species → Species → Species
(F ⊡ G) L = Σ FinSet (λ L₁ → Σ FinSet (λ L₂ →
              ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (F L₁ × G L₂)
            ))

lem-FinS≃ : (m : ℕ) → Fin (S m) ≃ (Fin m ⊎ ⊤)
lem-FinS≃ m = equiv f g fg gf
  where
    f : ∀ {m : ℕ} → Fin (S m) → (Fin m ⊎ ⊤)
    f fO     = inr unit
    f (fS x) = inl x
    g : ∀ {m : ℕ} → (Fin m ⊎ ⊤) → Fin (S m)
    g (inr _) = fO
    g (inl x) = fS x
    fg : ∀ {m : ℕ} → (b : Fin m ⊎ ⊤) → (f (g b) == b)
    fg (inr unit) = idp
    fg (inl x) = idp
    gf : ∀ {m : ℕ} → (b : Fin (S m)) → (g (f b) == b)
    gf fO = idp
    gf (fS x) = idp

lem-Fin≃ : (m n : ℕ) → (Fin m ≃ Fin n) → (m == n)
lem-Fin≃ O O e = idp
lem-Fin≃ O (S n) e = fO-elim (<– e fO)
lem-Fin≃ (S m) O e = fO-elim (–> e fO)
lem-Fin≃ (S m) (S n) e = ap S (lem-Fin≃ m n (gcbp (lem-FinS≃ n ∘e e ∘e lem-FinS≃ m ⁻¹) (ide ⊤)))

⊡pair : ∀ {F G : Species} {L₁ L₂ L : FinSet}
       → ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋)
       → F L₁ → G L₂ → (F ⊡ G) L
⊡pair {_} {_} {L₁} {L₂} iso f g
  = L₁ , (L₂ , (iso , (f , g)))

⊡-idL : ∀ {F : Species} → (One ⊡ F) == F
⊡-idL {F} = λ= (λ L → ua
  (equiv
    (f F L)
    (g F L)
    (fg F L)
    (gf F L)
  ))
  where
    f : (F : Species) → (L : FinSet) → (One ⊡ F) L → F L
    f _ _ (L₁ , (L₂ , (iso , (⊥≃L₁ , FL₂)))) = {!!}
    g : (F : Species) → (L : FinSet) → F L → (One ⊡ F) L
    g = {!!}
    fg : (F : Species) → (L : FinSet) → (x : F L) → (f F L (g F L x) == x)
    fg = {!!}
    gf : (F : Species) → (L : FinSet) → (x : (One ⊡ F) L) → (g F L (f F L x) == x)
    gf = {!!}

{-
      (One ⊡ F) == F
λ= :: ∀ L : FinSet . (One ⊡ F) L == F L
ua :: ∀ L : FinSet . (One ⊡ F) L ≃  F L
ua :: ∀ L : FinSet . ( Σ (L₁ L₂ : FinSet). ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (One L₁ × F L₂) ) ≃ F L
   :: ∀ L : FinSet . ( Σ (L₁ L₂ : FinSet). ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (⊥ ≃ ⌊ L₁ ⌋ × F L₂) ) ≃ F L

      ⌊ L ⌋ ≃ ⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋ ≃ ⊥ ⊎ ⌊ L₂ ⌋ ≃ ⌊ L₂ ⌋

      How to apply ⌊ L ⌋ ≃ ⌊ L₂ ⌋  to  F L₂  to get  F L ?

      Something is wrong here.

-}
