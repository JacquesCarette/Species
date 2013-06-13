module FinPf where

open import Data.Fin hiding ( _≤_ ; _<_ ; _+_ )
open import Data.Nat
open import Data.Product
open import Data.Sum
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

Fin→FinℕL : ∀ {n} → (f : Fin n) → f ≡ Finℕ→Fin (Fin→Finℕ f)
Fin→FinℕL zero = refl
Fin→FinℕL (suc f) rewrite (sym (Fin→FinℕL f)) = refl

-- Fin→FinℕR : ∀ {n} → (f : Finℕ n) → proj₁ f ≡ proj₁ (Fin→Finℕ (Finℕ→Fin f))
-- Fin→FinℕR (zero , s≤s i<n) = refl
-- Fin→FinℕR (suc i , s≤s i<n) rewrite (sym (Fin→FinℕR (i , i<n))) = refl

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

-- Need to do inverse of Finℕprod.  Involves doing a divmod operation.

--------------------------------------------------
-- Stuff for sums

Finℕsum : ∀ {m n} → (Finℕ m ⊎ Finℕ n) → Finℕ (m + n)
Finℕsum {m} {n} (inj₁ (i , i<m)) = i + n , +-mono {suc i} {m} i<m ≤-refl
Finℕsum {m} {n} (inj₂ (j , j<n)) = j , ≤-+R {suc j} {n} {m} j<n

+-OR : (n : ℕ) → (n + 0 ≡ n)
+-OR zero = refl
+-OR (suc n) = cong suc (+-OR n)

+-sucR : (m : ℕ) → (n : ℕ) → m + suc n ≡ suc (m + n)
+-sucR zero _ = refl
+-sucR (suc m) n rewrite (+-sucR m n) = refl

decLT : (n : ℕ) → (x : ℕ) → (x < n) ⊎ (Σ[ j ∈ ℕ ] (x ≡ j + n))
decLT zero x = inj₂ (x , sym (+-OR x))
decLT (suc n) zero = inj₁ (s≤s z≤n)
decLT (suc n) (suc x) with (decLT n x)
decLT (suc n) (suc x) | inj₁ x<n = inj₁ (s≤s x<n)
decLT (suc n) (suc x) | inj₂ (j , x≡j+n) rewrite x≡j+n = inj₂ (j , sym (+-sucR j n))

{-
cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl
-}

+-cancel : ∀ {m n} → (x : ℕ) → (m + x) ≤ (n + x) → m ≤ n
+-cancel {m} {n} zero pf rewrite (+-OR n) | (+-OR m) = pf
+-cancel {m} {n} (suc x) pf rewrite (+-sucR m x) | (+-sucR n x) = ≤-inj (+-cancel x pf)

FinℕsumInv : ∀ {m n} → Finℕ (m + n) → Finℕ m ⊎ Finℕ n
FinℕsumInv {m} {n} (x , x<m+n) with (decLT n x)
FinℕsumInv (x , x<m+n) | inj₁ x<n = inj₂ (x , x<n)
FinℕsumInv {m} {n} (x , x<m+n) | inj₂ (j , x≡j+n) rewrite x≡j+n = inj₁ (j , +-cancel n x<m+n)

--------------------------------------------------
-- Product inverse.

+-assoc : (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c = refl
+-assoc (suc a) b c rewrite (+-assoc a b c) = refl

+-comm : (a b : ℕ) → a + b ≡ b + a
+-comm zero b = sym (+-OR b)
+-comm (suc a) b rewrite (+-sucR b a) | +-comm a b = refl

divmod : (x : ℕ) → (n : ℕ) → Σ[ i ∈ ℕ ] ( Σ[ j ∈ ℕ ] ( (j < n) × ( x ≡ j + i * n ) ) )
divmod x n with decLT n x
divmod x n | inj₁ x<n = 0 , (x , x<n , (sym (+-OR x)))
divmod x n | inj₂ ( x' , x≡x'+n ) with divmod x' n  -- Agda can't see that x' < x
divmod x n | inj₂ (x' , x≡x'+n) | i' , j , j<n , x'≡j+i'*n
  rewrite x≡x'+n | x'≡j+i'*n | +-assoc j (i' * n) n | +-comm (i' * n) n
  = (suc i') , (j , (j<n , refl))

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans z≤n y≤z = z≤n
≤-trans (s≤s x≤y) (s≤s y≤z) = s≤s (≤-trans x≤y y≤z)

≤-<-trans : (x y z : ℕ) → x ≤ y → y < z → x < z
≤-<-trans x y z x≤y y<z = ≤-trans (s≤s x≤y) y<z

cancel-+-left-≤ : ∀ i {j k} → i + j ≤ i + k → j ≤ k
cancel-+-left-≤ zero    le       = le
cancel-+-left-≤ (suc i) (s≤s le) = cancel-+-left-≤ i le

cancel-*-right-≤ : ∀ i j k → i * suc k ≤ j * suc k → i ≤ j
cancel-*-right-≤ zero    _       _ _  = z≤n
cancel-*-right-≤ (suc i) zero    _ ()
cancel-*-right-≤ (suc i) (suc j) k le =
  s≤s (cancel-*-right-≤ i j k (cancel-+-left-≤ (suc k) le))

*-zeroR : ∀ x → x * 0 ≡ 0
*-zeroR zero = refl
*-zeroR (suc x) = *-zeroR x

*-cancelR : (i m n : ℕ) → i * n < m * n → i < m
*-cancelR i m zero () rewrite *-zeroR i | *-zeroR m
*-cancelR i m (suc n) im<mn = {!!}

-- cancel-*-right-≤ (suc i) m n {!≤-<-trans !}  -- {! ≤-<-trans (n + i * suc n) (i * suc n) (m * suc n) !}

FinℕprodInv : (m : ℕ) → (n : ℕ) → Finℕ (m * n) → Finℕ m × Finℕ n
FinℕprodInv m n (x , x<mn) with divmod x n
FinℕprodInv m n (x , x<mn) | i , j , j<n , x≡j+i*n
  rewrite x≡j+i*n
  = (i , *-cancelR i m n (≤-<-trans (i * n) (j + i * n) (m * n) (≤-+R {i * n} {i * n} {j} ≤-refl {- i * n -}) x<mn)) , (j , j<n)
