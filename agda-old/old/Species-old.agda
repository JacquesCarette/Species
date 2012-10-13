module Species where

open import Data.Empty
open import Data.Unit
open import Data.Product

open import Data.Bool
import Data.Fin as F
open import Data.Nat

open import Data.Vec

-- Universe of base types
data U : Set where
  Unit : U
  Nat  : U

ι : U -> Set
ι Unit = ⊤
ι Nat  = ℕ

ι⋆ : {n : ℕ} -> Vec U n -> Set
ι⋆ {zero} _ = ⊤
ι⋆ {suc n} (u ∷ us) = ι u × ι⋆ us

-- The species algebra.
data Species : ℕ -> Set where
  Zero : {n : ℕ} -> Species n
  One  : {n : ℕ} -> Species n
  K    : {n : ℕ} -> U -> Species n
  X    : {n : ℕ} -> (i : F.Fin n) -> Species n
  _⊕_  : {n : ℕ} -> Species n -> Species n -> Species n
  _⊙_  : {n : ℕ} -> Species n -> Species n -> Species n
  μ    : {n : ℕ} -> Species (suc n) -> Species n

  -- need a permutation operation, perhaps...



-- Interpreting species as polymorphic type constructors.
ty : {n : ℕ} -> {Us : Vec U n} -> Species n -> ι⋆ Us -> Set
ty {_} Zero _ = ⊥
ty {_} One _ = ⊤
ty {_} (K τ) _ = ι τ
ty {zero} (X ()) _
ty {suc n} {u ∷ us} (X F.zero) (τ , _) = {!!}
ty {_} (y ⊕ y') Us = {!!}
ty {_} (y ⊙ y') Us = {!!}
ty {_} (μ y) Us = {!!}
  
