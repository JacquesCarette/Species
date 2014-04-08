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

mutual
  data Code : Set where
    ⊥C : Code
    ⊤C : Code
    _⊎C_ : Code → Code → Code
    _×C_ : Code → Code → Code
    _→C_ : Code → Code → Code
    Ob : Code
    ∀C : (c : Code) → (⟦ c ⟧ → Code) → Code
      -- The c is there just so we can express the type of the
      -- function, which actually encodes the ∀.  Note we ignore the c
      -- in the definition of ⟦_⟧ below.

      -- Apparently this technique is folklore, but I learned it from
      -- https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf .

  ⟦_⟧ : Code → Set
  ⟦ ⊥C ⟧ = ⊥
  ⟦ ⊤C ⟧ = ⊤
  ⟦ c₁ ⊎C c₂ ⟧ = ⟦ c₁ ⟧ ⊎ ⟦ c₂ ⟧
  ⟦ c₁ ×C c₂ ⟧ = ⟦ c₁ ⟧ × ⟦ c₂ ⟧
  ⟦ c₁ →C c₂ ⟧ = ⟦ c₁ ⟧ → ⟦ c₂ ⟧
  ⟦ Ob ⟧ = {!!}
  ⟦ ∀C _ f ⟧ = (s : _) → ⟦ f s ⟧

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

-- module _ where
--   open import Categories.Agda
--   open import Categories.Functor
--   open import Data.Product

--   smallSetsHasEnds : HasEnds SmallSets SmallSets
--   smallSetsHasEnds = record
--     { end = λ F → record
--       { Data = record
--         { E = ∀C {!!} {!!}
--         ; π = {!!}
--         }
--       ; universal = {!!}
--       ; π[c]∘universal≡δ[c] = {!!}
--       ; universal-unique = {!!}
--       }
--     }
