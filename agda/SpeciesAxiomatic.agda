module SpeciesAxiomatic where

-- A "pride" is a collection of labels.
record Pride : Set₁ where
  field
    Carrier : Set

open Pride

-- Bijection between sets, should actually use something from the Agda standard library
postulate _≅_ : Set → Set → Set
postulate id≅ : {A : Set} → A ≅ A

-- We have some structure on the collection of all prides:
record _≃_ (P₁ : Pride) (P₂ : Pride) : Set where
  field
    iso : Carrier P₁ ≅ Carrier P₂

id≃ : {P : Pride} → P ≃ P
id≃ = record { iso = id≅ }

-- Theorem: (Pride, _≃_) is a groupoid.  This is an easy theorem at
-- the moment, but should be kept in mind as we change the definitions
-- of Pride and _≃_ in the future.

record Espece : Set₁ where
  field
    shapes    : Pride → Set
    relabel   : {P₁ P₂ : Pride} → P₁ ≃ P₂ → shapes P₁ ≅ shapes P₂
    -- Note we have a choice here whether to use shapes P₁ ≅ shapes P₂
    -- (as above), or shapes P₁ → shapes P₂.  I.e. which category is
    -- the target?  Since functors preserve isomorphisms, you can
    -- prove the above type as a theorem from a definition of relabel
    -- using →.  So we simply use _≅_ in the first place, since it is
    -- more powerful/convenient.

    -- isFunctor : (relabel id≃ ≡ id≅) × ?

open Espece

-- Abstract mappings.
postulate _↦_ : Set → Set → Set

record LabelledStruct (s : Espece) (p : Pride) (a : Set) : Set where
  field
    shp : shapes s p
    dat : Carrier p ↦ a
