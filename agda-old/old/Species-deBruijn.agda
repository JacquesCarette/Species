module Species-deBruijn where

open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum

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
ty : {n : ℕ} -> Species n -> Vec U n -> Set
ty Zero _ = ⊥
ty One _ = ⊤
ty (K t) _ = ι t
ty {zero} (X ()) _
ty {suc n} (X F.zero) (t ∷ _) = ι t
ty {suc n} (X (F.suc i)) (_ ∷ ts) = ty {n} (X i) ts
ty (S ⊕ T) ts = ty S ts ⊎ ty T ts
ty (S ⊙ T) ts = ty S ts × ty T ts
ty (μ S) ts = {!ty S !}   -- argh, have to do de Bruijn indices,
                          -- shifting, etc... OR use locally
                          -- nameless...
  
