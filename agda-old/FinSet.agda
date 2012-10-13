module FinSet where

open import Data.Empty
open import Data.Fin hiding (compare)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

open import Function.Inverse using (_↔_; Inverse)

open import Inverses using (_$⟩_; _⟨$_)
open import Pigeonhole

record FinSet : Set₁ where
  constructor finSet
  field
    Underlying : Set
    size       : ℕ
    isFinite   : Underlying ↔ Fin size

MkFin : ℕ -> FinSet
MkFin n = record 
        { Underlying = Fin n
        ; size = n
        ; isFinite = Function.Inverse.id }

-- Now we can show that if Fin n and Fin m are isomorphic, we must have n = m.

Fin-inj : ∀ {m n} → Fin n ↔ Fin m → n ≡ m
Fin-inj {m} {n}  iso with compare m n
Fin-inj {m} {._} iso | less .m k with pigeonhole (s≤s (m≤m+n m k)) (λ x → iso $⟩ x)
...                         | i , j , i≢j , pf = ⊥-elim (i≢j (Inverse.injective iso pf))
Fin-inj {m} {.m} iso | equal .m = refl
Fin-inj {._} {n} iso | greater .n k with pigeonhole (s≤s (m≤m+n n k)) (λ x → iso ⟨$ x)
...                         | i , j , i≢j , pf = ⊥-elim (i≢j (Inverse.injective (Function.Inverse.sym iso) pf))