-- open import Data.Nat
-- open import Data.Fin
-- open import Data.Sum
-- open import Data.Unit
-- open import Relation.Binary.PropositionalEquality

open import HoTT

module GCBP where

  data Fin : ℕ -> Set where
    fO : {n : ℕ} -> Fin (S n)
    fS : {n : ℕ} -> Fin n -> Fin (S n)

  record _⊆_ (A : Set) (B : Set) : Set where
    field
      embed : A -> B
      project : B -> Coprod Unit A
      rtL : (a : A) -> project (embed a) == inr a
      rtR : (b : B) (a : A) -> project b == inr a -> embed a == b

  Finite : Set -> Set
  Finite L = Σ ℕ (λ n → L ≃ Fin n)

  distributeR : {A : Set} {P Q : A -> Set}
             → Σ A (λ a → Coprod (P a) (Q a)) -> Coprod (Σ A P) (Σ A Q)
  distributeR (a , inl p) = inl (a , p)
  distributeR (a , inr q) = inr (a , q)

  distributeL : {A : Set} {P Q : A -> Set}
             → Coprod (Σ A P) (Σ A Q) -> Σ A (λ a → Coprod (P a) (Q a))
  distributeL (inl (a , p)) = a , inl p
  distributeL (inr (a , q)) = a , inr q

  distributeRL : {A : Set} {P Q : A -> Set} ->
    (b : Coprod (Σ A P) (Σ A Q)) -> distributeR (distributeL b) == b
  distributeRL (inl (_ , _)) = idp
  distributeRL (inr (_ , _)) = idp

  distributeLR : {A : Set} {P Q : A -> Set} ->
    (b : Σ A (λ a → Coprod (P a) (Q a))) -> distributeL (distributeR b) == b
  distributeLR (_ , inl _) = idp
  distributeLR (_ , inr _) = idp

  distribute : {A : Set} {P Q : A -> Set}
             → Σ A (λ a → Coprod (P a) (Q a)) ≃ Coprod (Σ A P) (Σ A Q)
  distribute = equiv distributeR distributeL distributeRL distributeLR

  module Defragment
           (L : Set)
           (n : ℕ)
           (sub : L ⊆ Fin n)
           (gcbp : {A B A' B' : Set} -> (Coprod A A' ≃ Coprod B B') -> (A ≃ B) -> (A' ≃ B')) where

    open _⊆_

    D1 : Set
    D1 = Coprod (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l)))
                (Σ (Fin n) (λ k → project sub k == inl unit))

    f1 : D1 -> Fin n
    f1 (inl (k , _)) = k
    f1 (inr (k , _)) = k

    g1' : Fin n -> Σ (Fin n) (λ k → Coprod (Σ L (λ l → project sub k == inr l))
                                           (project sub k == inl unit))
    g1' k = k , match_withl_withr_ {C = λ prj → Coprod (Σ L (λ l → prj == inr l))
                                                       (prj == inl unit) }
             (project sub k)
             (λ unit → inr idp)
             (λ l → inl (l , idp))

    g1 : Fin n -> D1
    g1 n = –> (distribute {P = λ k → Σ L (λ l → project sub k == inr l)}
                          {Q = λ k → project sub k == inl unit})
             (g1' n)

    f1g1 : (k : Fin n) → f1 (g1 k) == k
    f1g1 k = {!!}

    decomp1 : (s : ℕ) -> D1 ≃ Fin n
    decomp1 s = equiv f1 g1 f1g1 {!!}

    defragment : (Σ ℕ (λ n → L ⊆ Fin n)) -> Finite L
    defragment = {!!}
