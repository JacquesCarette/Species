module FinPf where

open import Data.Fin hiding ( _≤_ ; _<_ ; _+_ )
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

Finℕ : ℕ → Set
Finℕ n = Σ[ i ∈ ℕ ] (i < n)

Fin→Finℕ : ∀ {n} → Fin n → Finℕ n
Fin→Finℕ zero = zero , s≤s z≤n
Fin→Finℕ (suc n₁) with (Fin→Finℕ n₁)
Fin→Finℕ (suc n₁) | f , f<n₁ = (suc f) , (s≤s f<n₁)

Finℕ→Fin : ∀ {n} → Finℕ n → Fin n
Finℕ→Fin (zero , s≤s _) = zero
Finℕ→Fin (suc i , s≤s i<n) = suc (Finℕ→Fin (i , i<n))

Finℕprod : ∀ {m n} → Finℕ m → Finℕ n → Finℕ (m * n)
Finℕprod {zero} (_ , ()) _
Finℕprod {suc m} {n} (i , i<m) (j , j<n) = j + i * n , {!!}
  -- should be easy from here... we have
  --   suc j <= n
  --   suc i <= suc m   ==>   i <= m
  --
  -- hence
  --   suc j + i*n <= n + m*n
  --
  -- by congruence, QED.  Just a matter of finding all those things in
  -- the Agda library.  Not sure how much is needed to port this to Haskell.

finPair : ∀ {m n} → Fin m → Fin n → Fin (m * n)
finPair i j = Finℕ→Fin (Finℕprod (Fin→Finℕ i) (Fin→Finℕ j))

finPair_correct : ∀ {m n} → (i : Fin m) → (j : Fin n)
                → (toℕ (finPair i j) ≡ toℕ j + toℕ i * n)
finPair_correct = {!!}
