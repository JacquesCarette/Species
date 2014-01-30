{-# OPTIONS --without-K #-}

open import HoTT

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

-- FinSet --------------------------------------------------

-- syntax Σ A (λ a → B) = Σ[ a ∈ A ] B

IsFinite : Set → Set
IsFinite A = Σ ℕ (λ n → Fin n ≃ A)

FinSet : Set₁
FinSet = Σ Set IsFinite

-- Agda: \clL , \clR
⌊_⌋ : FinSet → Set
⌊ A , _ ⌋ = A

-- Agda: \[[ , \]]
⟦_⟧ : ℕ → FinSet
⟦ n ⟧ = Fin n , (n , ide (Fin n))

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

one : One ⟦ 0 ⟧
one = ⊥≃Fin0

-- X -----------------------------------

X : Species
X L = ⊤ ≃ ⌊ L ⌋

x : X ⟦ 1 ⟧
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

⊎-0L : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊎-0L = equiv ⊎-projR inr (λ _ → idp) ⊎-inrProjR
  where
    ⊎-projR : ∀ {A : Set} → (⊥ ⊎ A) → A
    ⊎-projR (inl ())
    ⊎-projR (inr a) = a
    ⊎-inrProjR : ∀ {A : Set} → (a : ⊥ ⊎ A) → inr (⊎-projR a) == a
    ⊎-inrProjR (inl ())
    ⊎-inrProjR (inr x) = idp

⊎-0R : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊎-0R = equiv ⊎-projL inl (λ _ → idp) ⊎-inlProjL
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

⊞-0L : ∀ {F : Species} → (Zero ⊞ F) == F
⊞-0L = λ= (λ _ → ua ⊎-0L)

⊞-0R : ∀ {F : Species} → (F ⊞ Zero) == F
⊞-0R = λ= (λ _ → ua ⊎-0R)

-- Product -----------------------------

-- \b.
_⊡_ : Species → Species → Species
(F ⊡ G) L = Σ FinSet (λ L₁ → Σ FinSet (λ L₂ →
              ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (F L₁ × G L₂)
            ))

-- The above doesn't type check: it complains about universe levels,
-- and rightly so.  The problem is that this definition is
-- impredicative: the label sets could themselves be species
-- structures.  (Of course, that is exactly how functor composition is
-- implemented!)  But turning on --type-in-type makes Agda
-- inconsistent.
