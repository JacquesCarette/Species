module Permutations where

open import Algebra
open import Function using (_on_) renaming (_∘_ to _∘f_)

open import Data.Fin
open import Data.List
open import Data.List.Any as Any using (Any)
open import Data.Nat
open import Data.Product using (Σ; _,_; proj₁) renaming (map to prodMap)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using (Vec; allFin; lookup)

open import Relation.Binary using (module Setoid)
open import Relation.Binary.PropositionalEquality
  using (setoid; module ≡-Reasoning; _≡_)
  renaming (refl to ≡-refl; sym to ≡-sym; cong to ≡-cong)
open ≡-Reasoning

open import Function.Inverse using ( Inverse; _↔_; id; _∘_; sym )
open import Function.Equality using ( _⟨$⟩_ )

open import Inverses

postulate ?? : ∀ {ℓ} -> {A : Set ℓ} -> A

-- A permutation is a bijection between two finite sets.
Permutation : ℕ -> Set
Permutation n = Fin n ↔ Fin n

-- Permute a vector.
permute : {n : ℕ} -> {A : Set} -> Permutation n -> Vec A n -> Vec A n
permute {n} p v = Data.Vec.map (λ i → lookup (p ⟨$ i) v) (allFin n)

-- Automorphisms on a set S form a group under composition.
AutoGroup : Set -> Group _ _
AutoGroup S = record 
  { Carrier = S ↔ S
  ; _≈_ = _≈_
  ; _∙_ = _∘_
  ; ε   = id
  ; _⁻¹ = Function.Inverse.sym
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isEquivalence = isEquivalence
        ; assoc = λ f g h x≡y → 
            ≡-cong (λ x → f $⟩ g $⟩ h $⟩ x) x≡y
  
        ; ∙-cong = λ {f g h i} → λ f≈g → λ h≈i → λ {x y} → λ x≡y → 
                     begin
                       f $⟩ h $⟩ x     ≡⟨ ≡-cong (λ x → f $⟩ h $⟩ x) x≡y ⟩
                       f $⟩ h $⟩ y     ≡⟨ ≡-cong (λ x → f $⟩ x) (h≈i ≡-refl) ⟩
                       f $⟩ i $⟩ y     ≡⟨ f≈g ≡-refl ⟩
                       g $⟩ i $⟩ y
                     ∎
        }  
      ; identity = (λ f x≡y → ≡-cong (λ x → f $⟩ x) x≡y) 
                 , (λ f x≡y → ≡-cong (λ x → f $⟩ x) x≡y)
      }
    ; inverse = (λ f {x y} x≡y → 
                   begin
                     f ⟨$ f $⟩ x       ≡⟨ Inverse.left-inverse-of f x ⟩
                     x                 ≡⟨ x≡y ⟩
                     y
                   ∎
                )
              , (λ f {x y} x≡y → 
                   begin
                     f $⟩ f ⟨$ x       ≡⟨ Inverse.right-inverse-of f x ⟩
                     x                 ≡⟨ x≡y ⟩
                     y
                   ∎
                )

      -- if (x=y) -> f x = g y (i.e. f = g), 
      -- then (x=y) -> f^-1 x = g^-1 y.
    ; ⁻¹-cong = λ {f g} → λ f≈g → λ {x y} → λ x≡y →
                  begin
                    f ⟨$ x             ≡⟨ ≡-sym (Inverse.left-inverse-of g (f ⟨$ x)) ⟩
                    g ⟨$ g $⟩ f ⟨$ x   ≡⟨ ≡-cong (λ z → g ⟨$ z) (≡-sym (f≈g ≡-refl)) ⟩
                    g ⟨$ f $⟩ f ⟨$ x   ≡⟨ ≡-cong (λ z → g ⟨$ z) (Inverse.right-inverse-of f x) ⟩
                    g ⟨$ x             ≡⟨ ≡-cong (λ z → g ⟨$ z) x≡y ⟩
                    g ⟨$ y
                  ∎

    } 
  }
  where 
    open Setoid (InverseSetoid (setoid S) (setoid S))

-- One particular example is the "symmetric group" of permutations on Fin n.
SymmGroup : ℕ -> Group _ _
SymmGroup n = AutoGroup (Fin n)

-- Subgroups via generators.

module GenSubgroup {ℓ₁ ℓ₂} (G : Group ℓ₁ ℓ₂) where
  open Any.Membership (Group.setoid G)
  open Group G

  swapGenPf : {gens : List (Group.Carrier G)}
       -> {g : Group.Carrier G}
       -> ( g ∈ gens ⊎ g ⁻¹ ∈ gens )
       -> ( g ⁻¹ ∈ gens ⊎ (g ⁻¹) ⁻¹ ∈ gens )
  swapGenPf (inj₁ x) = inj₂ ??
  swapGenPf (inj₂ y) = inj₁ y

  GenSubgroup : List (Group.Carrier G) -> Group _ _
  GenSubgroup gens = record 
    { Carrier = List (Σ (Group.Carrier G) (λ g → g ∈ gens ⊎ g ⁻¹ ∈ gens))
    ; _≈_     = _≈_ on (foldr _∙_ ε ∘f map proj₁)
    ; _∙_     = _++_
    ; ε       = []
    ; _⁻¹     = reverse ∘f map (prodMap _⁻¹ (swapGenPf {gens}))
    ; isGroup = record 
      { isMonoid = record 
        { isSemigroup = record 
          { isEquivalence = ??
          ; assoc = ??
          ; ∙-cong = ?? 
        }
        ; identity = (λ _ → refl) , (λ x → ??) 
        }
      ; inverse  = (λ x → ??) , (λ x → ??)
      ; ⁻¹-cong  = ?? 
      } 
    }

SymmSubgroup : (n : ℕ) -> List (Group.Carrier (SymmGroup n)) -> Group _ _
SymmSubgroup n gens = GenSubgroup gens
  where open GenSubgroup (SymmGroup n)

{-
sg-proj : {n : ℕ} -> {gens : List (Group.Carrier (SymmGroup n))} 
        -> Group.Carrier (SymmSubgroup n gens) -> Group.Carrier (SymmGroup n)
sg-proj = foldr _∙_ ε ∘f map proj₁
-}

{-
respects-perms : ∀ {A B} -> (n : ℕ) -> (List (Group.Carrier (SymmGroup n))) 
               -> (Vec A n -> B) -> Set
respects-perms {A} n gens f = ∀ (σ : Group.Carrier (SymmSubgroup n gens)) (xs : Vec A n) -> ?? -- f xs ≡ f (permute (?? σ) xs)
-}