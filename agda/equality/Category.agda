------------------------------------------------------------------------
-- 1-categories
------------------------------------------------------------------------

-- Based on a draft of the chapter "Category theory" from "Homotopy
-- Type Theory: Univalent Foundations of Mathematics". I think the
-- parts of this chapter that I make use of were written by Mike
-- Shulman.

open import Equality

module Category
  {reflexive} (eq : ∀ {a p} → Equality-with-J a p reflexive) where

open import Bijection eq hiding (id; _∘_; inverse; finally-↔)
open Derived-definitions-and-properties eq
open import Equivalence eq as Eq
  using (_≃_; ⟨_,_⟩; module _≃_; Is-equivalence)
open import Function-universe eq hiding (id) renaming (_∘_ to _⊚_)
open import H-level eq
open import H-level.Closure eq
open import Logical-equivalence using (module _⇔_)
open import Prelude as P hiding (id)
open import Univalence-axiom eq

------------------------------------------------------------------------
-- Precategories

Precategory′ : (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
Precategory′ ℓ₁ ℓ₂ =
  -- Objects.
  ∃ λ (Obj : Set ℓ₁) →

  -- Morphisms (a /set/).
  ∃ λ (HOM : Obj → Obj → SET ℓ₂) →
  let Hom = λ X Y → proj₁ (HOM X Y) in

  -- Identity.
  ∃ λ (id : ∀ {X} → Hom X X) →

  -- Composition.
  ∃ λ (_∙_ : ∀ {X Y Z} → Hom X Y → Hom Y Z → Hom X Z) →

  -- Identity laws.
  (∀ {X Y} {f : Hom X Y} → id ∙ f ≡ f) ×
  (∀ {X Y} {f : Hom X Y} → f ∙ id ≡ f) ×

  -- Associativity.
  (∀ {X Y Z U} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z U} →
     f ∙ (g ∙ h) ≡ (f ∙ g) ∙ h)

-- A wrapper.

record Precategory (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    precategory : Precategory′ ℓ₁ ℓ₂

  -- Objects.

  Obj : Set ℓ₁
  Obj = proj₁ precategory

  -- Morphisms.

  HOM : Obj → Obj → SET ℓ₂
  HOM = proj₁ (proj₂ precategory)

  -- The morphism type family.

  Hom : Obj → Obj → Set ℓ₂
  Hom X Y = proj₁ (HOM X Y)

  -- The morphism types are sets.

  Hom-is-set : ∀ {X Y} → Is-set (Hom X Y)
  Hom-is-set = proj₂ (HOM _ _)

  -- Identity.

  id : ∀ {X} → Hom X X
  id = proj₁ (proj₂ (proj₂ precategory))

  -- Composition.

  infixl 10 _∙_

  _∙_ : ∀ {X Y Z} → Hom X Y → Hom Y Z → Hom X Z
  _∙_ = proj₁ (proj₂ (proj₂ (proj₂ precategory)))

  -- The left identity law.

  left-identity : ∀ {X Y} {f : Hom X Y} → id ∙ f ≡ f
  left-identity = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ precategory))))

  -- The right identity law.

  right-identity : ∀ {X Y} {f : Hom X Y} → f ∙ id ≡ f
  right-identity =
    proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ precategory)))))

  -- The associativity law.

  assoc : ∀ {X Y Z U} {f : Hom X Y} {g : Hom Y Z} {h : Hom Z U} →
          f ∙ (g ∙ h) ≡ (f ∙ g) ∙ h
  assoc =
    proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ precategory)))))

  -- Isomorphisms.

  Is-isomorphism : ∀ {X Y} → Hom X Y → Set ℓ₂
  Is-isomorphism f = ∃ λ g → (f ∙ g ≡ id) × (g ∙ f ≡ id)

  infix 4 _≅_

  _≅_ : Obj → Obj → Set ℓ₂
  X ≅ Y = ∃ λ (f : Hom X Y) → Is-isomorphism f

  -- Some projections.

  infix 15 _¹ _⁻¹ _¹⁻¹ _⁻¹¹

  _¹ : ∀ {X Y} → X ≅ Y → Hom X Y
  f ¹ = proj₁ f

  _⁻¹ : ∀ {X Y} → X ≅ Y → Hom Y X
  f ⁻¹ = proj₁ (proj₂ f)

  _¹⁻¹ : ∀ {X Y} (f : X ≅ Y) → f ¹ ∙ f ⁻¹ ≡ id
  f ¹⁻¹ = proj₁ (proj₂ (proj₂ f))

  _⁻¹¹ : ∀ {X Y} (f : X ≅ Y) → f ⁻¹ ∙ f ¹ ≡ id
  f ⁻¹¹ = proj₂ (proj₂ (proj₂ f))

  abstract

    -- "Is-isomorphism f" is a proposition.

    Is-isomorphism-propositional :
      ∀ {X Y} (f : Hom X Y) →
      Is-proposition (Is-isomorphism f)
    Is-isomorphism-propositional f =
      _⇔_.from propositional⇔irrelevant
        λ { (g , fg , gf) (g′ , fg′ , g′f) →
            Σ-≡,≡→≡ (g             ≡⟨ sym left-identity ⟩
                     id ∙ g        ≡⟨ cong (λ h → h ∙ g) $ sym g′f ⟩
                     (g′ ∙ f) ∙ g  ≡⟨ sym assoc ⟩
                     g′ ∙ (f ∙ g)  ≡⟨ cong (_∙_ g′) fg ⟩
                     g′ ∙ id       ≡⟨ right-identity ⟩∎
                     g′            ∎)
                    (Σ-≡,≡→≡ (_⇔_.to set⇔UIP Hom-is-set _ _)
                             (_⇔_.to set⇔UIP Hom-is-set _ _)) }

    -- Isomorphism equality is equivalent to "forward morphism"
    -- equality.

    ≡≃≡¹ : ∀ {X Y} {f g : X ≅ Y} → (f ≡ g) ≃ (f ¹ ≡ g ¹)
    ≡≃≡¹ {f = f} {g} =
      (f ≡ g)      ↔⟨ inverse $ ignore-propositional-component $ Is-isomorphism-propositional _ ⟩□
      (f ¹ ≡ g ¹)  □

    -- The type of isomorphisms (between two objects) is a set.

    ≅-set : ∀ {X Y} → Is-set (X ≅ Y)
    ≅-set = Σ-closure 2 Hom-is-set
                      (λ _ → mono₁ 1 $ Is-isomorphism-propositional _)

  -- Identity isomorphism.

  id≅ : ∀ {X} → X ≅ X
  id≅ = id , id , left-identity , right-identity

  -- Composition of isomorphisms.

  infixl 10 _∙≅_

  _∙≅_ : ∀ {X Y Z} → X ≅ Y → Y ≅ Z → X ≅ Z
  f ∙≅ g = (f ¹ ∙ g ¹) , (g ⁻¹ ∙ f ⁻¹) , fg f g , gf f g
    where
    abstract
      fg : ∀ {X Y Z} (f : X ≅ Y) (g : Y ≅ Z) →
           (f ¹ ∙ g ¹) ∙ (g ⁻¹ ∙ f ⁻¹) ≡ id
      fg f g =
        (f ¹ ∙ g ¹) ∙ (g ⁻¹ ∙ f ⁻¹)  ≡⟨ sym assoc ⟩
        f ¹ ∙ (g ¹ ∙ (g ⁻¹ ∙ f ⁻¹))  ≡⟨ cong (_∙_ (f ¹)) assoc ⟩
        f ¹ ∙ ((g ¹ ∙ g ⁻¹) ∙ f ⁻¹)  ≡⟨ cong (λ h → f ¹ ∙ (h ∙ f ⁻¹)) $ g ¹⁻¹ ⟩
        f ¹ ∙ (id ∙ f ⁻¹)            ≡⟨ cong (_∙_ (f ¹)) left-identity ⟩
        f ¹ ∙ f ⁻¹                   ≡⟨ f ¹⁻¹ ⟩∎
        id                           ∎

      gf : ∀ {X Y Z} (f : X ≅ Y) (g : Y ≅ Z) →
           (g ⁻¹ ∙ f ⁻¹) ∙ (f ¹ ∙ g ¹) ≡ id
      gf f g =
        (g ⁻¹ ∙ f ⁻¹) ∙ (f ¹ ∙ g ¹)  ≡⟨ sym assoc ⟩
        g ⁻¹ ∙ (f ⁻¹ ∙ (f ¹ ∙ g ¹))  ≡⟨ cong (_∙_ (g ⁻¹)) assoc ⟩
        g ⁻¹ ∙ ((f ⁻¹ ∙ f ¹) ∙ g ¹)  ≡⟨ cong (λ h → g ⁻¹ ∙ (h ∙ g ¹)) $ f ⁻¹¹ ⟩
        g ⁻¹ ∙ (id ∙ g ¹)            ≡⟨ cong (_∙_ (g ⁻¹)) left-identity ⟩
        g ⁻¹ ∙ g ¹                   ≡⟨ g ⁻¹¹ ⟩∎
        id                           ∎

  -- The inverse of an isomorphism.

  infix 15 _⁻¹≅

  _⁻¹≅ : ∀ {X Y} → X ≅ Y → Y ≅ X
  f ⁻¹≅ = f ⁻¹ , f ¹ , f ⁻¹¹ , f ¹⁻¹

  -- Isomorphisms form a precategory.

  precategory-≅ : Precategory ℓ₁ ℓ₂
  precategory-≅ = record { precategory =
    Obj ,
    (λ X Y → (X ≅ Y) , ≅-set) ,
    id≅ , _∙≅_ ,
    _≃_.from ≡≃≡¹ left-identity ,
    _≃_.from ≡≃≡¹ right-identity ,
    _≃_.from ≡≃≡¹ assoc }

  -- Equal objects are isomorphic.

  ≡→≅ : ∀ {X Y} → X ≡ Y → X ≅ Y
  ≡→≅ = elim (λ {X Y} _ → X ≅ Y) (λ _ → id≅)

  -- "Computation rule" for ≡→≅.

  ≡→≅-refl : ∀ {X} → ≡→≅ (refl X) ≡ id≅
  ≡→≅-refl = elim-refl (λ {X Y} _ → X ≅ Y) _

  -- Rearrangement lemma for ≡→≅.

  ≡→≅-¹ :
    ∀ {X Y} (X≡Y : X ≡ Y) →
    ≡→≅ X≡Y ¹ ≡ elim (λ {X Y} _ → Hom X Y) (λ _ → id) X≡Y
  ≡→≅-¹ {X} = elim¹
    (λ X≡Y → ≡→≅ X≡Y ¹ ≡
             elim (λ {X Y} _ → Hom X Y) (λ _ → id) X≡Y)
    (≡→≅ (refl X) ¹                                  ≡⟨ cong _¹ ≡→≅-refl ⟩
     id≅ ¹                                           ≡⟨⟩
     id                                              ≡⟨ sym $ elim-refl (λ {X Y} _ → Hom X Y) _ ⟩∎
     elim (λ {X Y} _ → Hom X Y) (λ _ → id) (refl X)  ∎)

  -- A lemma that can be used to prove that ≡→≅ is an equivalence.

  ≡→≅-equivalence-lemma :
    ∀ {X} →
    (≡≃≅ : ∀ {Y} → (X ≡ Y) ≃ (X ≅ Y)) →
    _≃_.to ≡≃≅ (refl X) ≡ id≅ →
    ∀ {Y} → Is-equivalence (≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence-lemma {X} ≡≃≅ ≡≃≅-refl {Y} =
    Eq.respects-extensional-equality
      (elim¹ (λ X≡Y → _≃_.to ≡≃≅ X≡Y ≡ ≡→≅ X≡Y)
             (_≃_.to ≡≃≅ (refl X)  ≡⟨ ≡≃≅-refl ⟩
              id≅                  ≡⟨ sym ≡→≅-refl ⟩∎
              ≡→≅ (refl X)         ∎))
      (_≃_.is-equivalence ≡≃≅)

-- An example: sets and functions. (Defined using extensionality.)

precategory-Set :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Precategory (lsuc ℓ) ℓ
precategory-Set ℓ ext = record { precategory =

  -- Objects: sets.
  SET ℓ ,

  -- Morphisms: functions.
  (λ { (A , A-set) (B , B-set) →
       (A → B) , Π-closure ext 2 (λ _ → B-set) }) ,

  -- Identity.
  P.id ,

  -- Composition.
  (λ f g → g ∘ f) ,

  -- Laws.
  refl _ , refl _ , refl _ }

-- Isomorphisms in this category are equivalent to equivalences
-- (assuming extensionality).

≃≃≅-Set :
  (ℓ : Level) (ext : Extensionality ℓ ℓ) →
  let open Precategory (precategory-Set ℓ ext) in
  (X Y : Obj) → (Type X ≃ Type Y) ≃ (X ≅ Y)
≃≃≅-Set ℓ ext X Y = Eq.↔⇒≃ record
  { surjection = record
    { logical-equivalence = record
      { to   = λ X≃Y → _≃_.to X≃Y , _≃_.from X≃Y ,
                       ext (_≃_.left-inverse-of  X≃Y) ,
                       ext (_≃_.right-inverse-of X≃Y)
      ; from = λ X≅Y → Eq.↔⇒≃ record
                 { surjection = record
                   { logical-equivalence = record
                     { to   = proj₁ X≅Y
                     ; from = proj₁ (proj₂ X≅Y)
                     }
                   ; right-inverse-of = λ x →
                       cong (λ f → f x) $ proj₂ (proj₂ (proj₂ X≅Y))
                   }
                 ; left-inverse-of = λ x →
                     cong (λ f → f x) $ proj₁ (proj₂ (proj₂ X≅Y))
                 }
      }
    ; right-inverse-of = λ X≅Y →
        _≃_.from (≡≃≡¹ {X = X} {Y = Y}) (refl (proj₁ X≅Y))
    }
  ; left-inverse-of = λ X≃Y →
      Eq.lift-equality ext (refl (_≃_.to X≃Y))
  }
  where open Precategory (precategory-Set ℓ ext) using (≡≃≡¹)

------------------------------------------------------------------------
-- Categories

Category′ : (ℓ₁ ℓ₂ : Level) → Set (lsuc (ℓ₁ ⊔ ℓ₂))
Category′ ℓ₁ ℓ₂ =
  -- A precategory.
  ∃ λ (C : Precategory ℓ₁ ℓ₂) →

  -- The function ≡→≅ is an equivalence (for each pair of objects).
  ∀ {X Y} → Is-equivalence (Precategory.≡→≅ C {X = X} {Y = Y})

-- A wrapper.

record Category (ℓ₁ ℓ₂ : Level) : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    category : Category′ ℓ₁ ℓ₂

  -- Precategory.

  precategory : Precategory ℓ₁ ℓ₂
  precategory = proj₁ category

  open Precategory precategory public hiding (precategory)

  -- The function ≡→≅ is an equivalence (for each pair of objects).

  ≡→≅-equivalence : ∀ {X Y} → Is-equivalence (≡→≅ {X = X} {Y = Y})
  ≡→≅-equivalence = proj₂ category

  ≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)
  ≡≃≅ = ⟨ _ , ≡→≅-equivalence ⟩

  ≅→≡ : ∀ {X Y} → X ≅ Y → X ≡ Y
  ≅→≡ = _≃_.from ≡≃≅

  -- Obj has h-level 3.

  Obj-3 : H-level 3 Obj
  Obj-3 X Y =
    respects-surjection
      (_≃_.surjection (Eq.inverse ≡≃≅))
      2 ≅-set

  -- Isomorphisms form a category.

  category-≅ : Category ℓ₁ ℓ₂
  category-≅ = record { category = precategory-≅ , is-equiv }
    where
    module P≅ = Precategory precategory-≅

    abstract

      is-equiv : ∀ {X Y} → Is-equivalence (P≅.≡→≅ {X = X} {Y = Y})
      is-equiv (X≅Y , X≅Y-iso) =
        Σ-map (Σ-map
          P.id
          (λ {X≡Y} ≡→≅[X≡Y]≡X≅Y →
             elim (λ {X Y} X≡Y →
                     (X≅Y : X ≅ Y) (X≅Y-iso : P≅.Is-isomorphism X≅Y) →
                     ≡→≅ X≡Y ≡ X≅Y →
                     P≅.≡→≅ X≡Y ≡ (X≅Y , X≅Y-iso))
                  (λ X X≅X X≅X-iso ≡→≅[refl]≡X≅X →
                     P≅.≡→≅ (refl X)  ≡⟨ P≅.≡→≅-refl ⟩
                     P≅.id≅           ≡⟨ Σ-≡,≡→≡ (id≅           ≡⟨ sym ≡→≅-refl ⟩
                                                  ≡→≅ (refl X)  ≡⟨ ≡→≅[refl]≡X≅X ⟩∎
                                                  X≅X           ∎)
                                                 (_⇔_.to propositional⇔irrelevant (P≅.Is-isomorphism-propositional _) _ _) ⟩∎
                     (X≅X , X≅X-iso)  ∎)
                  X≡Y X≅Y X≅Y-iso
                  ≡→≅[X≡Y]≡X≅Y))
          (λ { {X≡Y , _} ∀y→≡y → λ { (X≡Y′ , ≡→≅[X≡Y′]≡X≅Y) →
             let lemma =
                   ≡→≅ X≡Y′             ≡⟨ elim (λ X≡Y′ → ≡→≅ X≡Y′ ≡ proj₁ (P≅.≡→≅ X≡Y′))
                                                (λ X → ≡→≅ (refl X)             ≡⟨ ≡→≅-refl ⟩
                                                       id≅                      ≡⟨ cong proj₁ $ sym P≅.≡→≅-refl ⟩∎
                                                       proj₁ (P≅.≡→≅ (refl X))  ∎)
                                                X≡Y′ ⟩
                   proj₁ (P≅.≡→≅ X≡Y′)  ≡⟨ cong proj₁ ≡→≅[X≡Y′]≡X≅Y ⟩∎
                   X≅Y                  ∎ in
             (X≡Y , _)   ≡⟨ Σ-≡,≡→≡ (cong proj₁ (∀y→≡y (X≡Y′ , lemma)))
                                    (_⇔_.to set⇔UIP P≅.≅-set _ _) ⟩∎
             (X≡Y′ , _)  ∎ } })
          (≡→≅-equivalence X≅Y)

  -- Some equality rearrangement lemmas.

  Hom-, : ∀ {X X′ Y Y′} {f : Hom X Y}
          (p : X ≡ X′) (q : Y ≡ Y′) →
          subst (uncurry Hom) (cong₂ _,_ p q) f ≡ ≡→≅ p ⁻¹ ∙ f ∙ ≡→≅ q ¹
  Hom-, p q = elim
    (λ p → ∀ q → ∀ {f} → subst (uncurry Hom) (cong₂ _,_ p q) f ≡
                         ≡→≅ p ⁻¹ ∙ f ∙ ≡→≅ q ¹)
    (λ X q → elim
       (λ q → ∀ {f} → subst (uncurry Hom) (cong₂ _,_ (refl X) q) f ≡
                      ≡→≅ (refl X) ⁻¹ ∙ f ∙ ≡→≅ q ¹)
       (λ Y {f} →
          subst (uncurry Hom) (cong₂ _,_ (refl X) (refl Y)) f  ≡⟨ cong (λ eq → subst (uncurry Hom) eq f) $ cong₂-refl _,_ ⟩
          subst (uncurry Hom) (refl (X , Y)) f                 ≡⟨ subst-refl (uncurry Hom) _ ⟩
          f                                                    ≡⟨ sym left-identity ⟩
          id ∙ f                                               ≡⟨ cong (λ g → g ⁻¹ ∙ f) $ sym ≡→≅-refl ⟩
          ≡→≅ (refl X) ⁻¹ ∙ f                                  ≡⟨ sym right-identity ⟩
          ≡→≅ (refl X) ⁻¹ ∙ f ∙ id                             ≡⟨ cong (λ g → ≡→≅ (refl X) ⁻¹ ∙ f ∙ g ¹) $ sym ≡→≅-refl ⟩∎
          ≡→≅ (refl X) ⁻¹ ∙ f ∙ ≡→≅ (refl Y) ¹                 ∎)
       q)
    p q

  ≡→≅-trans : ∀ {X Y Z} (p : X ≡ Y) (q : Y ≡ Z) →
              ≡→≅ (trans p q) ≡ ≡→≅ p ∙≅ ≡→≅ q
  ≡→≅-trans {X} = elim¹
    (λ p → ∀ q → ≡→≅ (trans p q) ≡ ≡→≅ p ∙≅ ≡→≅ q)
    (elim¹
       (λ q → ≡→≅ (trans (refl X) q) ≡ ≡→≅ (refl X) ∙≅ ≡→≅ q)
       (≡→≅ (trans (refl X) (refl X))  ≡⟨ cong ≡→≅ trans-refl-refl ⟩
        ≡→≅ (refl X)                   ≡⟨ ≡→≅-refl ⟩
        id≅                            ≡⟨ sym $ Precategory.left-identity precategory-≅ ⟩
        id≅ ∙≅ id≅                     ≡⟨ sym $ cong₂ _∙≅_ ≡→≅-refl ≡→≅-refl ⟩∎
        ≡→≅ (refl X) ∙≅ ≡→≅ (refl X)   ∎))

-- A lemma that can be used to turn a precategory into a category.

precategory-to-category :
  ∀ {c₁ c₂}
  (C : Precategory c₁ c₂) →
  let open Precategory C in
  (≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)) →
  (∀ {X} → _≃_.to ≡≃≅ (refl X) ≡ id≅) →
  Category c₁ c₂
precategory-to-category C ≡≃≅ ≡≃≅-refl = record
  { category = C , Precategory.≡→≅-equivalence-lemma C ≡≃≅ ≡≃≅-refl
  }

-- An example: sets and functions. (Defined using extensionality and
-- univalence.)

category-Set :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Univalence ℓ →
  Category (lsuc ℓ) ℓ
category-Set ℓ ext univ =
  precategory-to-category precategory ≡≃≅ ≡≃≅-refl-is-id≅
  where
  precategory = precategory-Set ℓ ext
  open Precategory precategory hiding (precategory)

  abstract

    -- _≡_ and _≅_ are pointwise equivalent…

    cong-Type : {X Y : Obj} → (X ≡ Y) ≃ (Type X ≡ Type Y)
    cong-Type = Eq.↔⇒≃ $ inverse $
      ignore-propositional-component (H-level-propositional ext 2)

    ≃≃≅ : (X Y : Obj) → (Type X ≃ Type Y) ≃ (X ≅ Y)
    ≃≃≅ = ≃≃≅-Set ℓ ext

    ≡≃≅ : ∀ {X Y} → (X ≡ Y) ≃ (X ≅ Y)
    ≡≃≅ {X} {Y} = ≃≃≅ X Y ⊚ ≡≃≃ univ ⊚ cong-Type

    -- …and the proof maps reflexivity to the identity isomorphism.

    ≡≃≅-refl-is-id≅ : ∀ {X} → _≃_.to ≡≃≅ (refl X) ≡ id≅ {X = X}
    ≡≃≅-refl-is-id≅ {X} =
      _≃_.to (≃≃≅ X X) (≡⇒≃ (proj₁ (Σ-≡,≡←≡ (refl X))))  ≡⟨ cong (_≃_.to (≃≃≅ X X) ∘ ≡⇒≃ ∘ proj₁) Σ-≡,≡←≡-refl ⟩
      _≃_.to (≃≃≅ X X) (≡⇒≃ (refl (Type X)))             ≡⟨ cong (_≃_.to (≃≃≅ X X)) ≡⇒≃-refl ⟩
      _≃_.to (≃≃≅ X X) Eq.id                             ≡⟨ _≃_.from (≡≃≡¹ {X = X} {Y = X}) (refl P.id) ⟩∎
      id≅ {X = X}                                        ∎

-- An example: sets and bijections. (Defined using extensionality and
-- univalence.)

category-Set-≅ :
  (ℓ : Level) →
  Extensionality ℓ ℓ →
  Univalence ℓ →
  Category (lsuc ℓ) ℓ
category-Set-≅ ℓ ext univ =
  Category.category-≅ (category-Set ℓ ext univ)

private

  -- The objects are sets.

  Obj-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ) (univ : Univalence ℓ) →
    Category.Obj (category-Set-≅ ℓ ext univ) ≡ SET ℓ
  Obj-category-Set-≅ _ _ _ = refl _

  -- The morphisms are bijections.

  Hom-category-Set-≅ :
    ∀ ℓ (ext : Extensionality ℓ ℓ) (univ : Univalence ℓ) →
    Category.Hom (category-Set-≅ ℓ ext univ) ≡
    Category._≅_ (category-Set ℓ ext univ)
  Hom-category-Set-≅ _ _ _ = refl _

------------------------------------------------------------------------
-- Functors

Functor′ : (ℓ₁ ℓ₂ : Level) → Precategory ℓ₁ ℓ₂ → Precategory ℓ₁ ℓ₂ → Set (ℓ₂ ⊔ ℓ₁)
Functor′ ℓ₁ ℓ₂ C D =
  let module C = Precategory C
      module D = Precategory D
  in

  -- Action on morphisms.
  ∃ λ (F₀ : C.Obj → D.Obj) →

  -- Action on homs.
  ∃ λ (F₁ : {a b : C.Obj} → (C.Hom a b) → (D.Hom (F₀ a) (F₀ b))) →

  -- Preserves identities.
  (∀ {X} → F₁ (C.id {X}) ≡ D.id {F₀ X}) ×

  -- Preserves composition.
  (∀ {X Y Z} {f : C.Hom X Y} {g : C.Hom Y Z} → F₁ (f C.∙ g) ≡ F₁ f D.∙ F₁ g)

record Functor (ℓ₁ ℓ₂ : Level) (C : Precategory ℓ₁ ℓ₂) (D : Precategory ℓ₁ ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    functor : Functor′ ℓ₁ ℓ₂ C D

  module C = Precategory C
  module D = Precategory D

  F₀ : C.Obj → D.Obj
  F₀ = proj₁ functor

  F₁ : ∀ {a b : C.Obj} → (C.Hom a b) → (D.Hom (F₀ a) (F₀ b))
  F₁ = proj₁ (proj₂ functor)

  F-identity : ∀ {X} → F₁ (C.id {X}) ≡ D.id {F₀ X}
  F-identity = proj₁ (proj₂ (proj₂ functor))

  F-composition : ∀ {X Y Z} {f : C.Hom X Y} {g : C.Hom Y Z} → F₁ (f C.∙ g) ≡ F₁ f D.∙ F₁ g
  F-composition = proj₂ (proj₂ (proj₂ functor))

------------------------------------------------------------------------
-- Natural transformations

NatTransf′ : (ℓ₁ ℓ₂ : Level) → {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Functor ℓ₁ ℓ₂ C D → Set (ℓ₁ ⊔ ℓ₂)
NatTransf′ ℓ₁ ℓ₂ {C} {D} F G =
  let open module D = Precategory D
      module F = Functor F
      module G = Functor G
  in

  -- Components
  ∃ λ (component : ∀ X → Hom (F.F₀ X) (G.F₀ X)) →

  -- Naturality
  (∀ {X Y} {f} → component X ∙ G.F₁ f ≡ F.F₁ f ∙ component Y)

record NatTransf (ℓ₁ ℓ₂ : Level) {C D : Precategory ℓ₁ ℓ₂} (F G : Functor ℓ₁ ℓ₂ C D) : Set (ℓ₁ ⊔ ℓ₂) where
  field
    natTransf : NatTransf′ ℓ₁ ℓ₂ F G

  open module D = Precategory D
  module F = Functor F
  module G = Functor G

  component : ∀ X → Hom (F.F₀ X) (G.F₀ X)
  component = proj₁ natTransf

  natural : ∀ {X Y} {f} → component X ∙ G.F₁ f ≡ F.F₁ f ∙ component Y
  natural = proj₂ natTransf

-- Convenient notation for the components of a natural transformation.
_[_] : ∀ {ℓ₁ ℓ₂ : Level} {C D : Precategory ℓ₁ ℓ₂} {F G : Functor ℓ₁ ℓ₂ C D} →
      (γ : NatTransf ℓ₁ ℓ₂ F G) → ∀ X → (Precategory.Hom D) (Functor.F₀ F X) (Functor.F₀ G X)
_[_] = NatTransf.component

-- Identity natural transformation on a functor F.
idNat : {ℓ₁ ℓ₂ : Level} {C D : Precategory ℓ₁ ℓ₂} {F : Functor ℓ₁ ℓ₂ C D} → NatTransf ℓ₁ ℓ₂ F F
idNat {D = D} =
  let open Precategory D in
  record { natTransf = (λ _ → id) , trans left-identity (sym right-identity) }

-- Composition of natural transformations.
compNat : {ℓ₁ ℓ₂ : Level} {C D : Precategory ℓ₁ ℓ₂} {F G H : Functor ℓ₁ ℓ₂ C D} →
          NatTransf ℓ₁ ℓ₂ F G → NatTransf ℓ₁ ℓ₂ G H → NatTransf ℓ₁ ℓ₂ F H
compNat {D = D} {F = F} {G = G} {H = H} γ η =
  let open Precategory D
      module F = Functor F
      module G = Functor G
      module H = Functor H
  in
  record { natTransf =
    -- Composition is componentwise.
    (λ X → γ [ X ] ∙ η [ X ]) ,

    -- Proof of naturality glues the two squares together.
    (λ {X} {Y} {f} →
      (γ [ X ] ∙ η [ X ]) ∙ H.F₁ f            ≡⟨ sym assoc ⟩
      γ [ X ] ∙ (η [ X ] ∙ H.F₁ f)            ≡⟨ cong (λ g → γ [ X ] ∙ g) (NatTransf.natural η) ⟩
      γ [ X ] ∙ (G.F₁ f ∙ η [ Y ])            ≡⟨ assoc ⟩
      (γ [ X ] ∙ G.F₁ f) ∙ η [ Y ]            ≡⟨ cong (λ g → g ∙ η [ Y ]) (NatTransf.natural γ) ⟩
      (F.F₁ f ∙ γ [ Y ]) ∙ η [ Y ]            ≡⟨ sym assoc ⟩∎
      F.F₁ f ∙ (γ [ Y ] ∙ η [ Y ])            ∎
    )
  }

-- Equality on natural transformations is determined by equality on
-- their components, since the naturality condition is a mere
-- proposition.
-- Note the other direction is (essentially) just Σ-≡,≡←≡ .
natTransf-≡ : ∀ {ℓ₁ ℓ₂ : Level} {C D : Precategory ℓ₁ ℓ₂} {F G : Functor ℓ₁ ℓ₂ C D} {γ η : NatTransf ℓ₁ ℓ₂ F G} →
  (∀ {ℓ₁ ℓ₂} → Extensionality ℓ₁ ℓ₂) → (∀ X → γ [ X ] ≡ η [ X ]) → γ ≡ η
natTransf-≡ {D = D} ext components-≡ =
  cong (λ nt → record { natTransf = nt })
    (Σ-≡,≡→≡
      (ext components-≡)
      (let open Precategory D in
         implicit-extensionality ext (λ _ →
         implicit-extensionality ext (λ _ →
         implicit-extensionality ext (λ _ →
         proj₁ (Hom-is-set _ _ _ _)))))
    )

{-   Is-set (Hom X Y)
   = H-level 2 (Hom X Y)
   = (x y : Hom X Y) → H-level 1 (x ≡ y)
   = (x y : Hom X Y) → (p q : x ≡ y) → H-level 0 (p ≡ q)
   = (x y : Hom X Y) → (p q : x ≡ y) → Contractible (p ≡ q)
   = (x y : Hom X Y) → (p q : x ≡ y) → (∃ λ (e : p ≡ q) → (∀ f → e ≡ f))
-}

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
cat-[_,_] C D {ext} = record { category =  precategory-[ C , proj₁ (D.category) ] {ext} , {!!} }
  where module D = Category D

-- A functor is full if it is a surjection from each hom-set
Is-full : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-full = {!!}

-- A functor is faithful if it is an injection from each hom-set
Is-faithful : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-faithful = {!!}

-- F : C -> D is split essentially surjective if for each d ∈ D, there
-- (constructively) exists c ∈ C such that F c ≅ d.
Is-split-essentially-surjective : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-split-essentially-surjective = {!!}

-- F : C -> D is essentially surjective if for each d ∈ D, there
-- *merely* exists c ∈ C such that F c ≅ d.
Is-essentially-surjective : ∀ {ℓ₁ ℓ₂} {C D : Precategory ℓ₁ ℓ₂} → Functor ℓ₁ ℓ₂ C D → Set {!!}
Is-essentially-surjective = {!!}
