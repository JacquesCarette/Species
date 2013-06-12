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
Fin→Finℕ (suc n₁) | f , f<n = (suc f) , s≤s f<n

Finℕ→Fin : ∀ {n} → Finℕ n → Fin n
Finℕ→Fin (zero , s≤s _) = zero
Finℕ→Fin (suc i , s≤s i<n) = suc (Finℕ→Fin (i , i<n))

≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-inj : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-inj (s≤s sm≤sn) = sm≤sn

≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc z≤n       = z≤n
≤-suc (s≤s m≤n) = s≤s (≤-suc m≤n)

≤-+R : ∀ {m n x} → m ≤ n -> m ≤ x + n
≤-+R {m} {n} {zero} m≤n = m≤n
≤-+R {m} {n} {suc x} m≤n = ≤-suc (≤-+R {m} {n} {x} m≤n)

+-mono : ∀ {m n x y} → m ≤ n → x ≤ y → (m + x) ≤ (n + y)
+-mono z≤n z≤n = z≤n
+-mono {zero} {n} {suc x} {suc y} z≤n (s≤s x≤y) = ≤-+R {suc x} {suc y} {n} (s≤s x≤y)
+-mono (s≤s m≤n) x≤y = s≤s (+-mono m≤n x≤y)

*-mono : ∀ {m n x y} → m ≤ n → x ≤ y -> (m * x) ≤ (n * y)
*-mono z≤n x≤y = z≤n
*-mono {suc m} {suc n} {x} {y} (s≤s m≤n) x≤y = +-mono {x} {y} {m * x} {n * y} x≤y (*-mono {m} {n} {x} {y} m≤n x≤y)

Finℕprod : ∀ {m n} → Finℕ m → Finℕ n → Finℕ (m * n)
Finℕprod {zero} (_ , ()) _
Finℕprod {suc m} {n} (i , i<m) (j , j<n) = j + i * n , +-mono {suc j} {n} {i * n} {m * n} j<n (*-mono {i} {m} {n} {n} (≤-inj i<m) ≤-refl)

finPair : ∀ {m n} → Fin m → Fin n → Fin (m * n)
finPair i j = Finℕ→Fin (Finℕprod (Fin→Finℕ i) (Fin→Finℕ j))

finPair_correct : ∀ {m n} → (i : Fin m) → (j : Fin n)
                → (toℕ (finPair i j) ≡ toℕ j + toℕ i * n)
finPair_correct i j = {!!}
