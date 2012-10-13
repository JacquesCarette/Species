{-# OPTIONS --type-in-type #-}

module Species where

open import Algebra

open import Level using (Lift)

open import Categories.Category
open import Categories.Functor

open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Product using ( _×_; Σ )
open import Data.Sum using ( _⊎_ )
open import Data.Unit using ( ⊤ )
open import Data.Vec

open import Function.Bijection
open import Function.Inverse renaming (_∘_ to _∘I_)

open import Relation.Binary

-- open import FinSet
open import Permutations

------------------------------------------------------------
-- The universe of species expressions
------------------------------------------------------------

data SPECIES : Set where
  ZERO : SPECIES
  ONE  : SPECIES

  MOL  : (n : ℕ) -> List (Group.Carrier (SymmGroup n)) -> SPECIES

  ∑    : (ℕ -> SPECIES) -> SPECIES

  _⊠_  : SPECIES -> SPECIES -> SPECIES
  _⊚_  : SPECIES -> SPECIES -> SPECIES

--  REC  : SPECIES

------------------------------------------------------------
-- The category 𝔹 of finite sets and bijections
------------------------------------------------------------

𝔹 : Category _ _ _
𝔹 = record 
  { Obj = Set
  ; _⇒_ = _↔_
  ; _≡_ = λ {A B} → {!(InverseSetoid (setoid A) (setoid B))._≈_!}
  ; id = Function.Inverse.id
  ; _∘_ = Function.Inverse._∘_
  ; assoc = {!!}
  ; identityˡ = {!!}
  ; identityʳ = {!!}
  ; equiv = record 
    { refl  = {!!}
    ; sym   = sym
    ; trans = {! trans !}
    }
  ; ∘-resp-≡ = {!!}
  }
  where open import Inverses

------------------------------------------------------------
-- Interpretation of species as endofunctors over 𝔹
------------------------------------------------------------

Species = Endofunctor 𝔹

One₀ : Set -> Set
One₀ U = (U ↔ Fin 0)
{-
One₀ (finSet _ zero _)    = MkFin 1
One₀ (finSet _ (suc n) _) = MkFin 0
-}

One₁ : {A B : Set} -> 𝔹 [ A , B ] -> 𝔹 [ One₀ A , One₀ B ]
One₁ {A} {B} A↔B = record 
  { to = {!!}
  ; from = record { _⟨$⟩_ = λ b↔Fin0 → b↔Fin0 ∘I A↔B; cong = {!!} }
  ; inverse-of = {!!} 
  }

{-
One₁ {finSet _ zero _} {finSet _ zero _}    f = Function.Inverse.id
One₁ {finSet UA zero finA} {finSet UB (suc n) finB} f 
  with Fin-inj (finB ∘I f ∘I sym finA)
...  | ()
One₁ {finSet UA (suc n) finA} {finSet UB zero finB} f
  with Fin-inj (finB ∘I f ∘I sym finA)
...  | ()
One₁ {finSet UA (suc n) finA} {finSet UB (suc n') finB} f = Function.Inverse.id
-}

⟦_⟧ : SPECIES -> Species
⟦ ZERO  ⟧ = record 
  { F₀ = λ _ → Fin 0
  ; F₁ = λ _ → Function.Inverse.id
  ; identity = Function.Inverse.id
  ; homomorphism = Function.Inverse.id
  ; F-resp-≡ = λ _ → Function.Inverse.id
  }
⟦ ONE   ⟧ = record 
  { F₀ = One₀
  ; F₁ = One₁
  ; identity = Function.Inverse.id
  ; homomorphism = Function.Inverse.id
  ; F-resp-≡ = λ _ → Function.Inverse.id
  }
⟦ MOL n gens ⟧ = {!!}  -- See BLL
⟦ ∑ f   ⟧      = {!!}
⟦ F ⊠ G ⟧      = {!!}
⟦ F ⊚ G ⟧      = {!!}
-- ⟦ REC   ⟧      = {!!}

------------------------------------------------------------
-- Interpretation of species as type constructors
------------------------------------------------------------

⟨_⟩_ : SPECIES -> Set -> Set
⟨ ZERO    ⟩ _ = ⊥
⟨ ONE     ⟩ _ = ⊤
⟨ MOL n _ ⟩ A = Vec A n  -- Σ Set (λ U → (U ↔ Fin n) × (U → A))
⟨ ∑ f     ⟩ A = Σ ℕ (λ n → ⟨ f n ⟩ A)
⟨ F ⊠ G   ⟩ A = ⟨ F ⟩ A × ⟨ G ⟩ A
⟨ F ⊚ G   ⟩ A = ⟨ F ⟩ (⟨ G ⟩ A)

elimArgs : SPECIES -> Set -> Set -> Set
elimArgs ZERO _ _ = ⊤
elimArgs ONE  _ B = B
elimArgs (MOL n gens) A B = Σ (Vec A n -> B) (λ f → {!respects-perms n gens f!})
elimArgs (∑ f)   A B = (n : ℕ) -> elimArgs (f n) A B
elimArgs (F ⊠ G) A B = elimArgs F A (elimArgs G A B)
elimArgs (F ⊚ G) A B = 
  Σ Set (λ C → elimArgs G A C × elimArgs F C B)


elimType : SPECIES -> Set -> Set -> Set
elimType F A B = elimArgs F A B -> ⟨ F ⟩ A -> B

elim : ∀ {A B} -> (F : SPECIES) -> elimType F A B
elim F = {!!}


{-

(f : Vec n A -> B) x (forall sigma in H. f xs = f (sigma xs)) -> (Mol n gens -> B)

() -> (⊥ A -> B)

B -> (⊤ A -> B)

((F A ~> B) x (G A ~> B) -> (F A + G A -> B)

((F A ~> C) x (G A ~> D) x ((C,D) -> B) -> (F A x G A -> B)

(F A -> A) -> mu F -> A

-}