module SizedSpecies where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.List

open import Data.Nat
open import Relation.Binary.PropositionalEquality

open import Algebra

Species = Monoid -> Set

data ZERO : Species where

data ONE : Species where
  One : ONE A 0

data X (A : Set) : ℕ -> Set where
  Id : A -> X A 1

data _⊕_ (F G : Species) (A : Set) : ℕ -> Set where
  inl : {n : ℕ} -> F A n -> (F ⊕ G) A n
  inr : {n : ℕ} -> G A n -> (F ⊕ G) A n

data _⊗_ (F G : Species) (A : Set) : ℕ -> Set where
  pair : {n₁ n₂ : ℕ} -> F A n₁ -> G A n₂ -> (F ⊗ G) A (n₁ + n₂)

data _∘_ (F G : Species) (A : Set) : ℕ -> Set where
  comp : {sizes : List ℕ} ->      -> (F ∘ G) A (sum sizes)

{-  Wrong!
Species = (ℕ -> Set) -> (ℕ -> Set)

a : ℕ -> Set
a 1 = ⊤
a _ = ⊥

Z : Species
Z _ _ = ⊥

I : Species
I _ 0 = ⊤
I _ _ = ⊥

X : Species
X F 1 = F 1
X _ _ = ⊥

data L (F : ℕ -> Set) : ℕ -> Set where
  nil  : L F 0
  cons : (m₁ m₂ : ℕ) -> (m₁ > 0) -> F m₁ -> L F m₂ -> L F (m₁ + m₂)

_⊕_ : Species -> Species -> Species
( F ⊕ G ) H n = F H n ⊎ G H n

_⊗_ : Species -> Species -> Species
( F ⊗ G ) H n = Σ ℕ (λ n₁ → Σ ℕ (λ n₂ → (n₁ + n₂ ≡ n) × F H n₁ × G H n₂))

Q : Species
Q = (X ⊗ L) ⊕ I

_≅_ : Species -> Species -> Set
F ≅ G = (n : ℕ) -> 

-- L F n = Σ ℕ (λ m₁ → Σ ℕ (λ m₂ → (m₁ > 0) × (m₁ + m₂ ≡ n) × F m₁ × L F m₂))
-}
