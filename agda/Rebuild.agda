{- The goal here is to ``rebuild'' labelled structures from as few assumptions 
   as possible.  As we go along, we explicitly state our assumptions, and
   justify any additional assumptions.

   What that entails is that many of the early definitions will be refined.
   As such, we will append (admitedly ugly) numbers to these definitions, to
   keep them distinct.
-}
module Rebuild where

open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality using (setoid)
open import Function.Inverse using (_↔_;id)

-- Requirements for each 'piece'
open import Data.Sum using (_⊎_) -- for species +
open import Data.Empty using (⊥) -- for emptyPride

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

-- First attempt.

-- a type of label sets is any type at all
record Pride : Set₁ where
  field
    Carrier : Set₀

record _≃_ (p₁ p₂ : Pride) : Set₁ where
  field
    relabelling : Pride.Carrier p₁ ↔ Pride.Carrier p₂

open Pride
open _≃_

-- This says that all prides have a Setoid (in fact Groupoid) structure
thm1 : ∀ {p : Pride} → Setoid _ _
thm1 = λ {p} → setoid (Carrier p)

-- note how we, rashly, choose Set₀ as our target.  This does matter!  Set₀ has a lot 
-- of structure, which we use [a little too implicitly].  So we might need to redo all
-- of this later, when we really do wish to be super-careful.
record Espece : Set₁ where
  field
    shape : Pride → Set₀
    relabel : {p₁ p₂ : Pride} → p₁ ≃ p₂ → shape p₁ ↔ shape p₂

open Espece

record Arr : Set₁ where
  field
    _↦_ : Pride → Set₀ → Set₀
    -- lookup is jumping ahead, as a Stack does not have it...
    lookup : {p : Pride} {a : Set₀} → p ↦ a → Carrier p → a

record LabelledStructure (a : Set₀) (p : Pride) (s : Espece) (arr : Arr) : Set₁ where
  open Arr arr
  field
    struct : (shape s) p
    dat : p ↦ a

postulate ⊎-pres-↔ : {A₁ B₁ A₂ B₂ : Set} → (A₁ ↔ B₁) → (A₂ ↔ B₂) → ((A₁ ⊎ A₂) ↔ (B₁ ⊎ B₂))

-- Note: ⊎
_+_ : Espece → Espece → Espece
e₁ + e₂ = record
  { shape = λ x → shape e₁ x ⊎ shape e₂ x 
  ; relabel = λ p≃q → ⊎-pres-↔ (relabel e₁ p≃q) (relabel e₂ p≃q)
  }

-- another assumption: we have the empty set available
emptyPride : Pride
emptyPride = record { Carrier = ⊥ } 

one : Espece
one = record -- because of size issues, we need the following
  { shape = λ x → Carrier x ↔ Carrier emptyPride 
  ; relabel = λ p≃q → {!!} -- long-winded but not difficult
  }

zero : Espece
zero = record
  { shape = λ _ → ⊥
  ; relabel = λ _ → id 
  }

-- For product, we'll need Pride co-product
_⊎P_ : Pride → Pride → Pride
p₁ ⊎P p₂ = record { Carrier = Carrier p₁ ⊎ Carrier p₂ }

-- here, things start to fall apart completely: we have massive level problems.
-- Intuitively, the problem is that Set is (way) too big for Prides.
_×_ : Espece → Espece → Espece
e₁ × e₂ = record 
  { shape = λ x → {!!} 
  ; relabel = {!!} 
  }
