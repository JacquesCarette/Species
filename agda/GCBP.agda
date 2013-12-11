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
      rtR : (b : B) -> (a : A) -> project b == inr a -> embed a == b

  Finite : Set -> Set
  Finite L = Σ ℕ (λ n → L ≃ Fin n)

  module Defragment
           (L : Set)
           (n : ℕ)
           (sub : L ⊆ Fin n)
           (gcbp : {A B A' B' : Set} -> (Coprod A A' ≃ Coprod B B') -> (A ≃ B) -> (A' ≃ B')) where

    defragment : (Σ ℕ (λ n → L ⊆ Fin n)) -> Finite L
    defragment = {!!}
