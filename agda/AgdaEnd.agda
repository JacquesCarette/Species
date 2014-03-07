module AgdaEnd where

import Level
lzero : Level.Level
lzero = Level.zero

open import Categories.Category
open import Categories.Bifunctor
open import Categories.End

record HasEnds {o ℓ e} (T : Category o ℓ e) : Set₁ where
  field
    end : {C : Category o ℓ e} → (F : Bifunctor (Category.op C) C T) → End {C = C} F

module _ where
  open import Categories.Agda
  open import Categories.Functor
  open import Data.Product

  setHasEnds : HasEnds (Sets lzero)
  setHasEnds = record
    { end = λ {C} F → record
      { Data = record
        { E = {!Category.Obj C!}  --(c : Category.Obj C) → Functor.F₀ F (c , c)
        ; π = {!!}
        }
      ; universal = {!!}
      ; π[c]∘universal≡δ[c] = {!!}
      ; universal-unique = {!!}
      }
    }
