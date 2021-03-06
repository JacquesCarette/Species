{- The goal here is to ``rebuild'' labelled structures from as few assumptions 
   as possible.  As we go along, we explicitly state our assumptions, and
   justify any additional assumptions.

   What that entails is that many of the early definitions will be refined.
   As such, we will append (admitedly ugly) numbers to these definitions, to
   keep them distinct.
-}

module Rebuild2 where

import Level
open import Relation.Binary.PropositionalEquality as P hiding ( [_] )
open import Function using (flip)
open import Data.Product using ( _,_ )

open import Categories.Category
-- open import Categories.Groupoid
open import Categories.Functor renaming (_∘_ to _∘F_ ; Functor to _⟶_)
open import Categories.Bifunctor
open import Categories.Object.BinaryCoproducts
open import Categories.Object.Initial
open import Categories.Object.BinaryProducts
open import Categories.Object.Terminal
open import Categories.Monoidal
open import Categories.Coend
open import Categories.Product using (Product ; πʳ)

-- Convenient abbreviations
lzero : Level.Level
lzero = Level.zero

Cat : Set₁
Cat = Category lzero lzero lzero

{- So what are the most basic ingredients of a labelled data structure?  We need
   all 3 ingredients of the name: labels, data, and ``structure''.  We view labels
   as indicating locations in the structure where the data goes.  [insert picture
   of a tree as a labelled structure here].

   Intuitively, it helps to keep the following idealized situation in mind: the
   labels and structure are known statically, and only the data is dynamic.  While
   not fully general, this situation turns out to occur rather frequently in
   practice, so it is worthwhile to explore it appropriately.

   So what is a single labelled structure?  It is some structure with a specific
   given collection of labels ``in'' that structure, indicating locations.  There
   are two (dual) ways to approach this:
   1. start with a structure and observe the locations.
   2. start with labels, and build a structure from that.

   #1 is the approach taken by the \emph{containers} crowd.  We want to explore
   the second route.  
-}

-- This is apparently (MacLane p. 224) equivalent to T being cocomplete.
record HasCoends {o ℓ e} (T : Category o ℓ e) : Set₁ where
  field
    coend : {C : Cat} → (F : Bifunctor (Category.op C) C T) → Coend {C = C} F

module _ where
  open import Categories.Agda  
  open import Categories.Functor
  open import Data.Product
  open import Data.Empty

  setHasCoends : HasCoends (Sets lzero)
  setHasCoends = record 
    { coend = λ {C} F → record
      { Data = record 
        { E = ⊤ -- Σ (Category.Obj C) (λ c → Functor.F₀ F (c , c))
        ; π = record 
          { α = {!!}
          ; commute = {!!}
          }
        }
      ; universal = {!!}
      ; π[c]∘universal≡δ[c] = {!!}
      ; universal-unique = {!!} 
      } 
    }

----------------------------------------------------------------------------------

-- Second attempt, using an ambient Groupoid
-- The Obj of the underlying category is the Pride, and the _⇒_ is 
-- the equivalence (that's why it is a Groupoid, not just a Category)
record AmbientGroupoid : Set₁ where
  field
    C : Cat
    -- G : Groupoid C
    additive : Monoidal C  -- needed for 1 and *

record TargetCategory (Amb : AmbientGroupoid) : Set₁ where
  field
    T : Cat
    coprod : BinaryCoproducts T  -- needed for _+_
    initial : Initial T                         -- needed for zero
    prod : BinaryProducts T         -- needed for _×_ , _∙_
    terminal : Terminal T               -- needed for e
    -- the objects of this (ShapeFamilies) need to "have elements"
    -- may need to be a Functor into Set-as-Cat
    hasCoends : HasCoends T    -- needed for _∙_

  private C = AmbientGroupoid.C Amb

  field
    elemsT : Category.Obj T → Set₀
    embedHom :  Category.Obj C → (C ⟶ T)
 
module Dummy (g : AmbientGroupoid)(c : TargetCategory g) where
    -- useful synonyms
    private
      Pride = Category.Obj (AmbientGroupoid.C g)
      _≈_ = Category._⇒_ (AmbientGroupoid.C g)
      ShapeFamily = Category.Obj (TargetCategory.T c)

    private module Tg = TargetCategory c
    private module Src = Category (AmbientGroupoid.C g)
    private module Trg = Category Tg.T

    open Category
    open Tg
    open Functor
    open AmbientGroupoid g

    Espece : Set _
    Espece = AmbientGroupoid.C g ⟶ TargetCategory.T c

    shape : Espece → Pride  → ShapeFamily
    shape = F₀
  
    relabel : (e : Espece) → ∀ {p₁ p₂} → p₁ ≈ p₂ → Tg.T [ (shape e p₁) , (shape e p₂) ]
    relabel = F₁ 

    -- This will require T to have co-products
    -- _+_ and zero below ought to give a monoidal structure on Espece
    -- if we added a homomorphism to generating functions, we could justify
    -- this name.
    _+_ : Espece → Espece → Espece
    e₁ + e₂ = record 
        { F₀ = λ x → (shape e₁ x) ∐ (shape e₂ x) 
        ;  F₁ = λ A⇒B → (relabel e₁ A⇒B) ⧻  (relabel e₂ A⇒B)
        ; identity = 
              begin
                (relabel e₁ Src.id) ⧻ (relabel e₂ Src.id)
              ↓⟨ []-cong₂ (Trg.∘-resp-≡ʳ (identity e₁)) (Trg.∘-resp-≡ʳ (identity e₂)) ⟩ 
                Trg.id ⧻ Trg.id
              ↓⟨ []-cong₂ Trg.identityʳ Trg.identityʳ ⟩
                [ i₁ , i₂ ]
              ↓⟨ η ⟩
                Trg.id
              ∎
        ; homomorphism = λ {_ _ _} {f} {g} →
              begin
                (relabel e₁ (C [ g ∘ f ]) ⧻ relabel e₂ (C [ g ∘ f ]))
              ↓⟨ []-cong₂ (Trg.∘-resp-≡ʳ (homomorphism e₁)) (Trg.∘-resp-≡ʳ (homomorphism e₂)) ⟩
                (T [ relabel e₁ g ∘ relabel e₁ f ] ⧻ T [ relabel e₂ g ∘ relabel e₂ f ])
              ↑⟨ ⧻∘⧻ ⟩
                (T [ relabel e₁ g ⧻ relabel e₂ g ∘ relabel e₁ f ⧻ relabel e₂ f ] )
              ∎
        ; F-resp-≡ = λ f≡g → []-cong₂ (Trg.∘-resp-≡ʳ (F-resp-≡ e₁ f≡g)) (Trg.∘-resp-≡ʳ (F-resp-≡ e₂ f≡g))
        }
        where 
          open BinaryCoproducts T coprod
          open Trg
          open Trg.HomReasoning

    -- Note the above development will probably work to lift any
    -- bifunctor on the target category.  For example, if the target
    -- category has products this construction yields Cartesian
    -- product on species (?)  Not sure of the details, but it seems
    -- like this could be generalized quite a bit.
    --
    -- The important point is to note what structure on D gets
    -- reflected in a functor category [C,D].

    zero : Espece
    zero = record 
      { F₀ = λ _ → ⊥ 
      ;  F₁ = λ _ → !
      ;  identity = !-unique Trg.id
      ;  homomorphism = !-unique (T [ ! ∘ ! ])
      ;  F-resp-≡ = λ _ → !-unique !
      }
      where
        open Initial T initial

    e : Espece
    e = record 
      { F₀ = λ _ → ⊤ 
      ;  F₁ = λ _ → !
      ;  identity = !-unique Trg.id
      ;  homomorphism = !-unique (T [ ! ∘ ! ])
      ;  F-resp-≡ = λ _ → !-unique !
      }
      where open Terminal T terminal

    -- Partitional product needs a lot of structure!
    --   * Coproducts in the source category
    --   * Ability to encode source morphisms as objects in the target category.
    --       Take source to be enriched over target?
    --   * Coends in the target category?
    -- See "Day convolution".
    _∙_  : Espece → Espece → Espece
    e₁ ∙ e₂  = coendF (record { F₀ = S }) 
                                (λ p → coend (S p))
      where
        open BinaryProducts T prod
        open Monoidal additive
        open HasCoends hasCoends
        C×C = Product C C
        G : Obj C → (C×C ⟶ T)
        G p = record 
          { F₀ = λ { (c , d) → (F₀ e₁ c × F₀ e₂ d) × F₀ (embedHom p) (F₀ ⊗ (c , d)) }
          ;  F₁ = λ {(f , g) → (F₁ e₁ f ⁂ F₁ e₂ g) ⁂ F₁ (embedHom p) (F₁ ⊗ (f , g))}
          ;  identity = {!!}
          ;  homomorphism = {!!}
          ;  F-resp-≡ = {!!}
          }
        S : Obj C → (Product (Category.op C×C) C×C) ⟶ T
        S p = G p ∘F πʳ
{-
record 
      { F₀ = coendF ?
      ;  F₁ = {!!}
      ;  identity = {!!}
      ;  homomorphism = {!!}
      ;  F-resp-≡ = {!!}
      }
-}

    one : Espece
    one = record 
      { F₀ = F₀ zero⇒
      ;  F₁ = F₁ zero⇒
      ;  identity = identity zero⇒
      ;  homomorphism = homomorphism zero⇒
      ;  F-resp-≡ = F-resp-≡ zero⇒
      }
      where zero⇒ = embedHom (Monoidal.id additive)

    record Storage : Set₁ where
      field
        ⌊_⌋ : Pride → Cat
        _↦_ : Pride → Cat → Set₀
        -- index is jumping ahead, as a Stack does not have it...
        -- somehow, this is not well motivated...
        index : {P : Pride} {Dat : Category _ _ _} → P ↦ Dat → (⌊ P ⌋ ⟶ Dat)

    record LabelledStructure (p : Pride) (s : Espece) (stor : Storage) (trg : Cat) : Set₁ where
      open Storage stor
      field
        struct : elemsT (shape s p)
        store : p ↦ trg
