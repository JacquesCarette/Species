module Species where

open import Function.Inverse
open import Data.Nat
open import Data.Product
open import Data.Fin
open import Function.Equality as F

IsFinite : Set -> Set
IsFinite A = Σ[ n ∈ ℕ ] Fin n ↔ A

FinSet : Set₁
FinSet = Σ[ A ∈ Set ] IsFinite A

record Species : Set₁ where
  field
    shapes  : FinSet → Set
    relabel : (FinSet ↔ FinSet) → (Set → Set)
    relabel_id : (L : FinSet) → relabel F.id =