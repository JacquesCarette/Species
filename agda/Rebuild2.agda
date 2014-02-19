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

open import Categories.Category
open import Categories.Groupoid
open import Categories.Functor
open import Categories.Object.BinaryCoproducts
open import Categories.Object.Initial

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

----------------------------------------------------------------------------------

-- Second attempt, using an ambient Groupoid
-- The Obj of the underlying category is the Pride, and the _⇒_ is 
-- the equivalence (that's why it is a Groupoid, not just a Category)
record AmbientGroupoid : Set₁ where
  field
    C : Category Level.zero Level.zero Level.zero
    G : Groupoid C
    -- objects have elements (we think this will evolve into a Functor)
    ⌊_⌋ : (Category.Obj C) → Set₀

record TargetCategory : Set₁ where
  field
    T : Category Level.zero Level.zero Level.zero
    -- this will likely evolve into a Functor too
    elemsT : Category.Obj T → Set₀
    coprod : BinaryCoproducts T  -- needed for _+_
    initial : Initial T                         -- needed for zero

module Dummy (g : AmbientGroupoid)(c : TargetCategory) where
    -- useful synonyms
    private
      Pride = Category.Obj (AmbientGroupoid.C g)
      _≈_ = Category._⇒_ (AmbientGroupoid.C g)
      Shape = Category.Obj (TargetCategory.T c)

    private module Tg = TargetCategory c
    private module Src = Category (AmbientGroupoid.C g)
    private module Trg = Category Tg.T

    open Category
    open Tg
    open Functor
    open AmbientGroupoid g

    Espece : Set _
    Espece = Functor (AmbientGroupoid.C g) (TargetCategory.T c)

    shape : Espece → Pride  → Shape
    shape = F₀
  
    relabel : (e : Espece) → ∀ {p₁ p₂} → p₁ ≈ p₂ → Tg.T [ (shape e p₁) , (shape e p₂) ]
    relabel = F₁ 

    record Arr : Set₁ where
      field
        _↦_ : Pride → Set₀ → Set₀
        -- lookup is jumping ahead, as a Stack does not have it...
        -- somehow, this is not well motivated...
        lookup : {p : Pride} {a : Set₀} → p ↦ a → ⌊ p ⌋ → a


    record LabelledStructure (a : Set₀) (p : Pride) (s : Espece) (arr : Arr) : Set₁ where
      open Arr arr
      field
        struct : elemsT (shape s p)
        dat : p ↦ a

{-
postulate ⊎-pres-↔ : {A₁ B₁ A₂ B₂ : Set} → (A₁ ↔ B₁) → (A₂ ↔ B₂) → ((A₁ ⊎ A₂) ↔ (B₁ ⊎ B₂))
-} 

    -- This will require T to have co-products
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

    -- Partitional product needs a lot of structure!
    --   * Coproducts in the source category
    --   * Ability to encode source morphisms as objects in the target category.
    --       Take source to be enriched over target?
    --   * Coends in the target category?
    -- See "Day convolution".
    _∙_  : Espece → Espece → Espece
    e₁ ∙ e₂  = record 
      { F₀ = λ P → {!!}
      ;  F₁ = {!!}
      ;  identity = {!!}
      ;  homomorphism = {!!}
      ;  F-resp-≡ = {!!}
      }

    one : Espece
    one = record 
      { F₀ = {!!}
      ;  F₁ = {!!}
      ;  identity = {!!}
      ;  homomorphism = {!!}
      ;  F-resp-≡ = {!!}
      }


{-
-- another assumption: we have the empty set available
emptyPride : Pride
emptyPride = record { Carrier = ⊥ } 



-- For product, we'll need Pride co-product
_⊎P_ : Pride → Pride → Pride
p₁ ⊎P p₂ = record { Carrier = Carrier p₁ ⊎ Carrier p₂ }

_×_ : Espece → Espece → Espece
e₁ × e₂ = record 
  { shape = λ x → {!!} 
  ; relabel = {!!} 
  }

-}
