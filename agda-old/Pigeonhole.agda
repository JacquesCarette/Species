-- Pigeonhole principle
-- Code from copumpkin and xplat.

module Pigeonhole where

open import Data.Fin hiding (compare) renaming (_<_ to _<ᶠⁱⁿ_)
open import Data.Fin.Props
open import Data.Fin.Dec
open import Data.Nat
open import Data.Product

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)

open import Function

private
  drop-suc : ∀ {o} {m n : Fin o} →
             suc m ≡ (suc n ∶ Fin (suc o)) → m ≡ n
  drop-suc refl = refl

punchout : ∀ {m} (i j : Fin (suc m)) → i ≢ j → Fin m
punchout zero zero i≢j with i≢j refl
... | ()
punchout zero (suc j) i≢j = j
punchout {zero} (suc ()) j i≢j
punchout {suc n} (suc i) zero i≢j = zero
punchout {suc n} (suc i) (suc j) i≢j = suc (punchout i j (i≢j ∘ cong suc))

punchout-inj : ∀ {m} {i j k : Fin (suc m)} (i≢j : i ≢ j) (i≢k : i ≢ k)
             → (punchout i j i≢j ≡ punchout i k i≢k) → j ≡ k
punchout-inj {m} {zero} {zero} i≢j i≢k pj≡pk with i≢j refl
... | ()
punchout-inj {m} {zero} {suc j} {zero} i≢j i≢k pj≡pk with i≢k refl
... | ()
punchout-inj {m} {zero} {suc j} {suc k} i≢j i≢k pj≡pk = cong suc pj≡pk
punchout-inj {zero} {suc ()} i≢j i≢k pj≡pk
punchout-inj {suc n} {suc i} {zero} {zero} i≢j i≢k pj≡pk = refl
punchout-inj {suc n} {suc i} {zero} {suc k} i≢j i≢k ()
punchout-inj {suc n} {suc i} {suc j} {zero} i≢j i≢k ()
punchout-inj {suc n} {suc i} {suc j} {suc k} i≢j i≢k pj≡pk
  = cong suc (punchout-inj (i≢j ∘ cong suc) (i≢k ∘ cong suc) (drop-suc pj≡pk))

punchouts : ∀ {m n} (f : Fin n → Fin (suc m)) (i : Fin (suc m))
          → ∄ (λ j → i ≡ f j) → (Fin n → Fin m)
punchouts f i ∄j[i≡fj] j = punchout i (f j) (λ i≡fj → ∄j[i≡fj] (j , i≡fj)) 

pigeonhole : ∀ {m n} (m<n : m < n) (f : Fin n → Fin m) → ∃₂ (λ i j → i ≢ j × f i ≡ f j)
pigeonhole (s≤s z≤n) f with f zero
pigeonhole (s≤s z≤n) f | ()
pigeonhole (s≤s (s≤s m≤n)) f with any? (Data.Fin.Props._≟_ (f zero) ∘ f ∘ suc)
pigeonhole (s≤s (s≤s m≤n)) f | yes (j , f0≡f[1+j])
  = zero , suc j , (λ()) , f0≡f[1+j]
pigeonhole (s≤s (s≤s m≤n)) f | no ∄k[f0≡f[1+k]] = fixup answer
  where
  f′ = punchouts (f ∘ suc) (f zero) ∄k[f0≡f[1+k]]

  answer = pigeonhole (s≤s m≤n) f′

  fixup : ∃₂ (λ i j → i ≢ j × f′ i ≡ f′ j) → ∃₂ (λ i j → i ≢ j × f i ≡ f j)
  fixup (    i ,     j , i≢j            ,              fi≡fj)
      = (suc i , suc j , i≢j ∘ drop-suc , punchout-inj (∄k[f0≡f[1+k]] ∘ ,_)
                                                       (∄k[f0≡f[1+k]] ∘ ,_)
                                                       fi≡fj)
