module SmallSets where

open import Data.Nat
open import Data.Empty
open import Data.Unit using (⊤)
open import Data.Sum
open import Data.Product

open import Categories.Support.PropositionalEquality
open import Categories.Category
open import Categories.Bifunctor
open import Categories.End

data Code′ (S : Set) : Set where
  ⊥C : Code′ S
  ⊤C : Code′ S
  _⊎C_ : Code′ S → Code′ S → Code′ S
  _×C_ : Code′ S → Code′ S → Code′ S
  _→C_ : Code′ S → Code′ S → Code′ S
  ∀C : (S → Code′ S) → Code′ S

⟦_⟧′ : ∀ {S} → Code′ S → Set
⟦ ⊥C ⟧′ = ⊥
⟦ ⊤C ⟧′ = ⊤
⟦ c₁ ⊎C c₂ ⟧′ = ⟦ c₁ ⟧′ ⊎ ⟦ c₂ ⟧′
⟦ c₁ ×C c₂ ⟧′ = ⟦ c₁ ⟧′ × ⟦ c₂ ⟧′
⟦ c₁ →C c₂ ⟧′ = ⟦ c₁ ⟧′ → ⟦ c₂ ⟧′
⟦ ∀C c ⟧′ = (s : _) → ⟦ c s ⟧′

Code′arg : (n : ℕ) → Set
Code′arg zero    = ⊥
Code′arg (suc n) = Code′ (Code′arg n)

Codeℕ : Set
Codeℕ = Σ[ n ∈ ℕ ] (Code′ (Code′arg n))

⟦_⟧ℕ : Codeℕ → Set
⟦ (n , c) ⟧ℕ = ⟦ c ⟧′

injArg : ∀ {n} → Code′arg n → Code′arg (suc n)
injArg {zero} a = ⊥-elim a
injArg {suc n} ⊥C = ⊥C
injArg {suc n} ⊤C = ⊤C
injArg {suc n} (a ⊎C a₁) = {!!}
injArg {suc n} (a ×C a₁) = {!!}
injArg {suc n} (a →C a₁) = {!!}
injArg {suc n} (∀C x) = ∀C (λ x₁ → {!!})

-- cum : ∀ {m n} → (m ≤ n) → code′ m → code′ n
-- cum z≤n c = {!!}
-- cum (s≤s pf) c = {!!}

Code : Set
Code = Code′ Codeℕ

⟦_⟧ : Code → Set
⟦_⟧ = ⟦_⟧′

-- demote : Code → CodeF
-- demote ⊥C = 0 , ⊥C
-- demote ⊤C = 0 , ⊤C
-- demote (c₁ ⊎C c₂) with demote c₁ | demote c₂
-- demote (c₁ ⊎C c₂) | n₁ , cf₁ | n₂ , cf₂ = {!!}
-- demote (c₁ ×C c₂) = {!!}
-- demote (c₁ →C c₂) = {!!}
-- demote (∀C x) = {!!}

embed : Codeℕ → Code
embed (n , ⊥C) = ⊥C
embed (n , ⊤C) = ⊤C
embed (n , c₁ ⊎C c₂) = embed (n , c₁) ⊎C embed (n , c₂)
embed (n , c₁ ×C c₂) = embed (n , c₁) ×C embed (n , c₂)
embed (n , c₁ →C c₂) = embed (n , c₁) →C embed (n , c₂)
embed (n , ∀C x) = ∀C (λ cn → {!!})

SmallSets : Category _ _ _
SmallSets = record
  { Obj = Code
  ; _⇒_ = λ c₁ c₂ → ⟦ c₁ ⟧ → ⟦ c₂ ⟧
  ; _≡_ = λ f g → ∀ {x} → f x ≣ g x
  ; _∘_ = λ f g x → f (g x)
  ; id = λ x → x

  ; assoc = ≣-refl
  ; identityˡ = ≣-refl
  ; identityʳ = ≣-refl
  ; equiv = record { refl = ≣-refl; sym = s; trans = t }
  ; ∘-resp-≡ = ∘-resp-≡′
  }
  where
  s : {A B : Set} → {i j : A → B} → ({x : A} → i x ≣ j x) → {x : A} → j x ≣ i x
  s f {x} rewrite f {x} = ≣-refl

  t : {A B : Set} {i j k : A → B} → ({x : A} → i x ≣ j x) → ({x : A} → j x ≣ k x) → {x : A} → i x ≣ k x
  t f g {x} rewrite f {x} | g {x} = ≣-refl

  ∘-resp-≡′ : {A B C : Set} {f h : B → C} {g i : A → B} →
             (∀ {x} → f x ≣ h x) →
             (∀ {x} → g x ≣ i x) →
             (∀ {x} → f (g x) ≣ h (i x))
  ∘-resp-≡′ {g = g} f≡h g≡i {x} rewrite f≡h {g x} | g≡i {x} = ≣-refl

record HasEnds {o ℓ e} (C : Category o ℓ e) (T : Category o ℓ e) : Set₁ where
  field
    end : (F : Bifunctor (Category.op C) C T) → End {C = C} F

module _ where
  open import Categories.Agda
  open import Categories.Functor
  open import Data.Product

  smallSetsHasEnds : HasEnds SmallSets SmallSets
  smallSetsHasEnds = record
    { end = λ F → record
      { Data = record
        { E = ∀C (λ c → Functor.F₀ F (embed c , embed c))
        ; π = record { α = λ c x → {!!}; commute = {!!} }
        }
      ; universal = {!!}
      ; π[c]∘universal≡δ[c] = {!!}
      ; universal-unique = {!!}
      }
    }
