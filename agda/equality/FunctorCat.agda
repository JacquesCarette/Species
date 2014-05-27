------------------------------------------------------------------------
-- 1-categories
------------------------------------------------------------------------

-- Based on a draft of the chapter "Category theory" from "Homotopy
-- Type Theory: Univalent Foundations of Mathematics". I think the
-- parts of this chapter that I make use of were written by Mike
-- Shulman.

open import Equality

module FunctorCat
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

-- open import Bijection eq hiding (id; _∘_; inverse; finally-↔)
open Derived-definitions-and-properties eq
-- open import Equivalence eq as Eq
--   using (_≃_; ⟨_,_⟩; module _≃_; Is-equivalence)
-- open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
-- open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id)
-- open import Univalence-axiom eq
open import Category eq

------------------------------------------------------------------------
-- Functor (pre)categories

lemma : ∀ {ℓ₁ ℓ₂ : Level} {C D : Precategory ℓ₁ ℓ₂} {F G : Functor ℓ₁ ℓ₂ C D} →
  H-level 2 (NatTransf′ ℓ₁ ℓ₂ F G) → H-level 2 (NatTransf ℓ₁ ℓ₂ F G)
lemma h = {!!}   -- Seems obviously true, not sure how to prove it

-- The precategory [C,D] of functors C -> D.
precategory-[_,_]
  : {ℓ₁ ℓ₂ : Level}
  → Precategory ℓ₁ ℓ₂
  → Precategory ℓ₁ ℓ₂
  → {ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂}
  → Precategory (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂)
precategory-[_,_] {ℓ₁} {ℓ₂} C D {ext} = record { precategory =

  -- Objects: functors.
  Functor ℓ₁ ℓ₂ C D ,

  -- Morphisms: natural transformations.
  (λ F G → NatTransf ℓ₁ ℓ₂ F G ,

           lemma (

           -- Type of natural transformations is a set, since
           Σ-closure 2

             -- the type of each component is a set,
             (Π-closure ext 2 (λ X → Precategory.Hom-is-set D))

             -- and the naturality condition is a mere proposition (hence a set),
             (λ _ → mono₁ 1

               -- since it is an equality between morphisms, and Hom is a set.
               (implicit-Π-closure ext 1
               (λ _ → implicit-Π-closure ext 1
               (λ _ → implicit-Π-closure ext 1
               (λ _ → Precategory.Hom-is-set D _ _)))))
           )
  ) ,

  -- Identity.
  (λ {F} → idNat {F = F}) ,

  -- Composition.
  compNat ,

  -- Laws follow from the category laws in D + extensionality.
  let open Precategory D in
    -- Left identity
    natTransf-≡ ext (λ _ → left-identity) ,

    -- Right identity.
    natTransf-≡ ext (λ _ → right-identity) ,

  -- Associativity.
    natTransf-≡ ext (λ _ → assoc)
  }

_iff_ : ∀ {ℓ₁ : Level} → Set ℓ₁ → Set ℓ₁ → Set ℓ₁
P iff Q = (P → Q) × (Q → P)

-- Some theorems about functor (pre)categories.
module FunctorCatThms {ℓ₁ ℓ₂ : Level} (ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) (C D : Precategory ℓ₁ ℓ₂) where

  module D^C = Precategory (precategory-[ C , D ] {ext})
  module D   = Precategory D

  -- Lemma 9.2.4.  A natural transformation is an isomorphism in a
  -- functor precategory D^C iff each component is an isomorphism in
  -- D.
  natural-iso↔components-iso : ∀ {F G : Functor ℓ₁ ℓ₂ C D} →
    (γ : NatTransf ℓ₁ ℓ₂ F G) → (D^C.Is-isomorphism γ) iff (∀ X → D.Is-isomorphism (γ [ X ]))
  natural-iso↔components-iso {F} {G} γ =
    (λ { (δ , γδ≡id , δγ≡id) → λ X →
           δ [ X ]
         , ( γ [ X ] D.∙ δ [ X ]                  ≡⟨⟩
             (compNat γ δ) [ X ]                  ≡⟨ cong (λ η → η [ X ]) γδ≡id ⟩
             (idNat {F = F}) [ X ]                ≡⟨ refl D.id ⟩∎
             D.id ∎
           )
         , ( δ [ X ] D.∙ γ [ X ]                  ≡⟨⟩
             (compNat δ γ) [ X ]                  ≡⟨ cong (λ η → η [ X ]) δγ≡id ⟩
             (idNat {F = G}) [ X ]                ≡⟨ refl D.id ⟩∎
             D.id ∎
           )
       }
    ) ,
    ( λ δ
        → (record { natTransf =
            (λ X → proj₁ (δ X)) ,
            ( λ {X} {Y} {f} →
              let module F = Functor F
                  module G = Functor G
              in
              proj₁ (δ X) D.∙ F.F₁ f                                      ≡⟨ sym D.right-identity ⟩
              proj₁ (δ X) D.∙ F.F₁ f D.∙ D.id                             ≡⟨ cong (λ g → proj₁ (δ X) D.∙ F.F₁ f D.∙ g)
                                                                                  (sym (proj₁ (proj₂ (δ Y)))) ⟩
              proj₁ (δ X) D.∙ F.F₁ f D.∙ (γ [ Y ] D.∙ proj₁ (δ Y))        ≡⟨ D.assoc ⟩
              proj₁ (δ X) D.∙ F.F₁ f D.∙ γ [ Y ] D.∙ proj₁ (δ Y)          ≡⟨ cong (λ g → g D.∙ _) (sym D.assoc) ⟩
              proj₁ (δ X) D.∙ (F.F₁ f D.∙ γ [ Y ]) D.∙ proj₁ (δ Y)        ≡⟨ cong (λ g → _ D.∙ g D.∙ _) (sym (NatTransf.natural γ)) ⟩
              proj₁ (δ X) D.∙ (γ [ X ] D.∙ G.F₁ f) D.∙ proj₁ (δ Y)        ≡⟨ cong (λ g → g D.∙ _) D.assoc ⟩
              proj₁ (δ X) D.∙ γ [ X ] D.∙ G.F₁ f D.∙ proj₁ (δ Y)          ≡⟨ cong (λ g → g D.∙ _ D.∙ _) (proj₂ (proj₂ (δ X))) ⟩
              D.id D.∙ G.F₁ f D.∙ proj₁ (δ Y)                             ≡⟨ sym D.assoc ⟩
              D.id D.∙ (G.F₁ f D.∙ proj₁ (δ Y))                           ≡⟨ D.left-identity ⟩∎
              G.F₁ f D.∙ proj₁ (δ Y) ∎
            )
          })
        , (natTransf-≡ ext (λ X → proj₁ (proj₂ (δ X))))
        , (natTransf-≡ ext (λ X → proj₂ (proj₂ (δ X))))
    )

{- One goal of this development is to formalize anafunctors in HoTT,
   and show they are equivalent to functors.  This is both a nice
   illustration of the power of doing category theory in HoTT, and
   also (I hope) sheds some light on some situations computationally:
   in particular there are certain functors (e.g. the one from B -> P)
   which are not obvious how to define, but can be defined as
   anafunctors; composing with the equivalence to functors shows how
   to construct the functor.

   What follows is a (certainly incomplete) roadmap of what still
   needs to be done to get there.

  - Prove that D^C is a category whenever D is (theorem 9.2.5 in the
    HoTT book). Note that

    * 'idtoiso' in the book is spelled ≡→≅ above, and conversely for isotoid.
    * Lemma 9.1.9 in the book is called Hom-,

    Completing the proof may require proving more supporting lemmas
    about idtoiso (e.g. equations 9.1.11-13 in the book).

  - For functors, define
    * composition (9.2.6, 9.2.9, 9.2.10)
    * full (9.4.3)
    * faithful (9.4.3)
    * (split) essential surjectivity (9.4.4, 9.4.6)

  - Formalize adjunctions (9.3.1, 9.3.2) and (adjoint) equivalence of
    categories (9.4.1).

  - Prove that a fully faithful, essentially surjective functor is an
    equivalence of categories. (9.4.5)

  - Formalize an anafunctor C -> D (for C,D precategories) as
    * a precategory X
    * a fully faithful, essentially surjective functor X -> C
    * a functor X -> D

  - Prove that (under suitable assumptions about things being
    categories instead of just precategories) the type of anafunctors
    is equivalent to the type of functors.  See my thesis document for
    a proof sketch.  Note this requires 9.4.5 above, as well as
    possibly some extra lemmas about transport of equivalences of
    categories.

  - Construct the categories P and B, and apply the above construction
    to yield a functor B -> P.
-}

-- theorem 9.2.5
cat-[_,_]
  : {ℓ₁ ℓ₂ : Level}
  → Precategory ℓ₁ ℓ₂
  → Category ℓ₁ ℓ₂
  → {ext : ∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂}
  → Category (ℓ₁ ⊔ ℓ₂) (ℓ₁ ⊔ ℓ₂)
cat-[_,_] C D {ext} = precategory-to-category C⇒D {!!} {!!}
  where module D = Category D
        C⇒D = precategory-[ C , D.precategory ] {ext}

-- A functor is full if it is a surjection from each hom-set
Is-full : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set (ℓ₁ ⊔ ℓ₂)
Is-full {C = C} {D} F = ∀ {X Y} → {!!}

-- A functor is faithful if it is an injection from each hom-set
Is-faithful : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set (ℓ₂ ⊔ ℓ₁)
Is-faithful {C = C} {D} F = ∀ {X Y} → (f g : C.Hom X Y) → (F.F₁ f) ≡ (F.F₁ g)
  where
    module C = Precategory C
    module D = Precategory D
    module F = Functor F

-- F : C -> D is split essentially surjective if for each d ∈ D, there
-- (constructively) exists c ∈ C such that F c ≅ d.
Is-split-essentially-surjective : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-split-essentially-surjective F = {!!}

-- F : C -> D is essentially surjective if for each d ∈ D, there
-- *merely* exists c ∈ C such that F c ≅ d.
Is-essentially-surjective : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-essentially-surjective F = {!!}
