-- NOTE: need to compile with +RTS -K200M -RTS or so.  Normal-size
-- stack doesn't cut it.

module Monoidal where

open import Data.Product using ( _,_ ; proj₁ ; proj₂ )
open import Data.Fin

open import Categories.Bifunctor using (Bifunctor)
open import Categories.Category
open import Categories.Monoidal using (Monoidal ; module Monoidal)
open import Categories.Product using (Product)
open import Categories.Object.BinaryProducts
open import Categories.Object.Terminal
open import Categories.NaturalIsomorphism

module ProductMonoid {o ℓ e} (C : Category o ℓ e) (P : BinaryProducts C) (T : Terminal C) where

  open import Categories.Monoidal.Helpers
  open MonoidalHelperFunctors

  open BinaryProducts C P
  open Terminal C T
  module C = Category C
  open C
  open Equiv
  open HomReasoning

  .prodF-id : ∀ {A B : Obj} → _⁂_ {A} {_} {B} id id ≡ id
  prodF-id =
    begin
      id ⁂ id
    ↓⟨ refl ⟩
      ⟨ id ∘ π₁ , id ∘ π₂ ⟩
    ↓⟨ ⟨⟩-cong₂ identityˡ identityˡ ⟩
      ⟨ π₁ , π₂ ⟩
    ↓⟨ η ⟩
      id
    ∎

  .prodF-hom : ∀ {X Y Z : Category.Obj (Product C C)} {f : Product C C [ X , Y ]} {g : Product C C [ Y , Z ]}
    → C [ proj₁ (Product C C [ g ∘ f ]) ⁂ proj₂ (Product C C [ g ∘ f ])
    ≡ C [ proj₁ g ⁂ proj₂ g ∘ proj₁ f ⁂ proj₂ f ] ]
  prodF-hom = sym ⁂∘⁂

  .prodF-resp : ∀ {A B : Category.Obj (Product C C)} {F G : Product C C [ A , B ]}
    → Product C C [ F ≡ G ] → C [ proj₁ F ⁂ proj₂ F ≡ proj₁ G ⁂ proj₂ G ]
  prodF-resp (F₁≡G₁ , F₂≡G₂) = ⁂-cong₂ F₁≡G₁ F₂≡G₂

  prodF : Bifunctor C C C
  prodF = record
    { F₀ = λ { (x , y) → x × y }
    ; F₁ = λ { (f , g) → f ⁂ g }
    ; identity = prodF-id
    ; homomorphism = prodF-hom
    ; F-resp-≡ = prodF-resp
    }

  ._⟩,⟨_ : ∀ {A B C} → {f f′ : C ⇒ A} {g g′ : C ⇒ B} → f ≡ f′ → g ≡ g′ → ⟨ f , g ⟩ ≡ ⟨ f′ , g′ ⟩

  _⟩,⟨_ = ⟨⟩-cong₂

  .⟨!,id⟩-commute : ∀ {X Y} {f : C [ X , Y ]} →
    ⟨ ! , id ⟩ ∘ f ≡ (id ⁂ f) ∘ ⟨ ! , id ⟩
  ⟨!,id⟩-commute {_} {_} {f} =
    begin
      ⟨ ! , id ⟩ ∘ f
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ ! ∘ f , id ∘ f ⟩
    ↓⟨ sym (!-unique (! ∘ f)) ⟩,⟨ identityˡ ⟩
      ⟨ ! , f ⟩
    ↑⟨ identityˡ ⟩,⟨ identityʳ ⟩
      ⟨ id ∘ ! , f ∘ id ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      (id ⁂ f) ∘ ⟨ ! , id ⟩
    ∎

  .⟨id,!⟩-commute : ∀ {X Y} {f : C [ X , Y ]} →
    ⟨ id , ! ⟩ ∘ f ≡ (f ⁂ id) ∘ ⟨ id , ! ⟩
  ⟨id,!⟩-commute {_} {_} {f} =
    begin
      ⟨ id , ! ⟩ ∘ f
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ id ∘ f , ! ∘ f ⟩
    ↓⟨ identityˡ ⟩,⟨ sym (!-unique (! ∘ f)) ⟩
      ⟨ f , ! ⟩
    ↑⟨ identityʳ ⟩,⟨ identityˡ ⟩
      ⟨ f ∘ id , id ∘ ! ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      (f ⁂ id) ∘ ⟨ id , ! ⟩
    ∎

  left-id : NaturalIsomorphism (id⊗x C prodF ⊤) (x C prodF ⊤)
  left-id = record
    { F⇒G = record
      { η = λ _ → π₂
      ; commute = λ _ → π₂∘⁂
      }
    ; F⇐G = record
      { η = λ _ → ⟨ ! , id ⟩
      ; commute = λ _ → ⟨!,id⟩-commute
      }
    ; iso = λ _ → record
      { isoˡ =
        begin
          ⟨ ! , id ⟩ ∘ π₂
        ↓⟨ ⟨⟩∘ ⟩
          ⟨ ! ∘ π₂ , id ∘ π₂ ⟩
        ↓⟨ ⟨⟩-cong₂ (sym (!-unique (! ∘ π₂))) identityˡ ⟩
          ⟨ ! , π₂ ⟩
        ↓⟨ ⟨⟩-congˡ (!-unique π₁) ⟩
          ⟨ π₁ , π₂ ⟩
        ↓⟨ η ⟩
          id
        ∎
      ; isoʳ = commute₂
      }
    }

  right-id : NaturalIsomorphism (x⊗id C prodF ⊤) (x C prodF ⊤)
  right-id = record
    { F⇒G = record
      { η = λ _ → π₁
      ; commute = λ _ → π₁∘⁂
      }
    ; F⇐G = record
      { η = λ _ → ⟨ id , ! ⟩
      ; commute = λ _ → ⟨id,!⟩-commute
      }
    ; iso = λ _ → record
      { isoˡ =
        begin
          ⟨ id , ! ⟩ ∘ π₁
        ↓⟨ ⟨⟩∘ ⟩
          ⟨ id ∘ π₁ , ! ∘ π₁ ⟩
        ↓⟨ ⟨⟩-cong₂ identityˡ (sym (!-unique (! ∘ π₁))) ⟩
          ⟨ π₁ , ! ⟩
        ↓⟨ ⟨⟩-congʳ (!-unique π₂) ⟩
          ⟨ π₁ , π₂ ⟩
        ↓⟨ η ⟩
          id
        ∎
      ; isoʳ = commute₁
      }
    }

{-

      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ∘
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      ≡
      ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

-}

  .prod-assoc-commuteˡ : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} {h : X₃ ⇒ Y₃} →
    ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      ≡
    ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
  prod-assoc-commuteˡ {_} {_} {_} {_} {_} {_} {f} {g} {h} =
    begin
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      ⟩
    ↓⟨ assoc ⟩,⟨ ⟨⟩∘ ⟩
      ⟨ π₁ ∘ π₁ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      , ⟨ (π₂ ∘ π₁) ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
        , π₂ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
        ⟩
      ⟩
    ↓⟨ (∘-resp-≡ʳ commute₁) ⟩,⟨ (assoc ⟩,⟨ commute₂) ⟩
      ⟨ π₁ ∘ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁
      , ⟨ π₂ ∘ π₁ ∘ ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
        , h ∘ π₂
        ⟩
      ⟩
    ↓⟨ (sym assoc) ⟩,⟨ ((∘-resp-≡ʳ commute₁) ⟩,⟨ refl) ⟩
      ⟨ (π₁ ∘ ⟨ f ∘ π₁ , g ∘ π₂ ⟩) ∘ π₁
      , ⟨ π₂ ∘ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁
        , h ∘ π₂
        ⟩
      ⟩
    ↓⟨ (∘-resp-≡ˡ commute₁) ⟩,⟨ (⟨⟩-congˡ (sym assoc)) ⟩
      ⟨ (f ∘ π₁) ∘ π₁ , ⟨ (π₂ ∘ ⟨ f ∘ π₁ , g ∘ π₂ ⟩) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ↓⟨ assoc ⟩,⟨ (⟨⟩-congˡ (∘-resp-≡ˡ commute₂)) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ (g ∘ π₂ ) ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ↓⟨ ⟨⟩-congʳ (⟨⟩-congˡ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁ , ⟨ g ∘ π₂ ∘ π₁ , h ∘ π₂ ⟩ ⟩
    ↑⟨ ⟨⟩-congʳ ((∘-resp-≡ʳ commute₁) ⟩,⟨ (∘-resp-≡ʳ commute₂)) ⟩
      ⟨ f ∘ π₁ ∘ π₁
      , ⟨ g ∘ π₁ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ , h ∘ π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ⟩
    ↑⟨ ⟨⟩-congʳ (assoc ⟩,⟨ assoc) ⟩
      ⟨ f ∘ π₁ ∘ π₁
      , ⟨ (g ∘ π₁) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ , (h ∘ π₂) ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ⟩
    ↑⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
      ⟨ f ∘ π₁ ∘ π₁
      , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩
      ⟩
    ↑⟨ (∘-resp-≡ʳ commute₁) ⟩,⟨ (∘-resp-≡ʳ commute₂) ⟩
      ⟨ f ∘ π₁ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ⟩
    ↑⟨ assoc ⟩,⟨ assoc ⟩
      ⟨ (f ∘ π₁) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      , (⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂) ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ∎

{-

      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      ∘
      ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      ≡
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩
      ∘
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩

-}

  .prod-assoc-commuteʳ : ∀ {X₁ X₂ X₃ Y₁ Y₂ Y₃} {f : X₁ ⇒ Y₁} {g : X₂ ⇒ Y₂} {h : X₃ ⇒ Y₃} →
    ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      ≡
    ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
  prod-assoc-commuteʳ {_} {_} {_} {_} {_} {_} {f} {g} {h} =
    begin
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      , (π₂ ∘ π₂) ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      ⟩
    ↓⟨ ⟨⟩∘ ⟩,⟨ assoc ⟩
      ⟨ ⟨ π₁ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
        , (π₁ ∘ π₂) ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
        ⟩
      , π₂ ∘ π₂ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
      ⟩
    ↓⟨ (commute₁ ⟩,⟨ assoc) ⟩,⟨ (∘-resp-≡ʳ commute₂) ⟩
      ⟨ ⟨ f ∘ π₁
        , π₁ ∘ π₂ ∘ ⟨ f ∘ π₁ , ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂ ⟩
        ⟩
      , π₂ ∘ ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂
      ⟩
    ↓⟨ (⟨⟩-congʳ (∘-resp-≡ʳ commute₂)) ⟩,⟨ (sym assoc) ⟩
      ⟨ ⟨ f ∘ π₁
        , π₁ ∘ ⟨ g ∘ π₁ , h ∘ π₂ ⟩ ∘ π₂
        ⟩
      , (π₂ ∘ ⟨ g ∘ π₁ , h ∘ π₂ ⟩) ∘ π₂
      ⟩
    ↓⟨ (⟨⟩-congʳ (sym assoc)) ⟩,⟨ (∘-resp-≡ˡ commute₂) ⟩
      ⟨ ⟨ f ∘ π₁
        , (π₁ ∘ ⟨ g ∘ π₁ , h ∘ π₂ ⟩) ∘ π₂
        ⟩
      , (h ∘ π₂) ∘ π₂
      ⟩
    ↓⟨ (⟨⟩-congʳ (∘-resp-≡ˡ commute₁)) ⟩,⟨ assoc ⟩
      ⟨ ⟨ f ∘ π₁ , (g ∘ π₁) ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ↓⟨ ⟨⟩-congˡ (⟨⟩-congʳ assoc) ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₁ ∘ π₂ ⟩ , h ∘ π₂ ∘ π₂ ⟩
    ↑⟨ ⟨⟩-congˡ ((∘-resp-≡ʳ commute₁) ⟩,⟨ (∘-resp-≡ʳ commute₂)) ⟩
      ⟨ ⟨ f ∘ π₁ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
        , g ∘ π₂ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
        ⟩
      , h ∘ π₂ ∘ π₂
      ⟩
    ↑⟨ ⟨⟩-congˡ (assoc ⟩,⟨ assoc) ⟩
      ⟨ ⟨ (f ∘ π₁) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
        , (g ∘ π₂) ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
        ⟩
      , h ∘ π₂ ∘ π₂
      ⟩
    ↑⟨ ⟨⟩-congˡ ⟨⟩∘ ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ ⟨ π₁ , π₁ ∘ π₂ ⟩
      , h ∘ π₂ ∘ π₂
      ⟩
    ↑⟨ (∘-resp-≡ʳ commute₁) ⟩,⟨ (∘-resp-≡ʳ commute₂) ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      , h ∘ π₂ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      ⟩
    ↑⟨ assoc ⟩,⟨ assoc ⟩
      ⟨ (⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      , (h ∘ π₂) ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
      ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ ⟨ f ∘ π₁ , g ∘ π₂ ⟩ ∘ π₁ , h ∘ π₂ ⟩ ∘ ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ , π₂ ∘ π₂ ⟩
    ∎

  prod-assoc : NaturalIsomorphism ([x⊗y]⊗z C prodF ⊤) (x⊗[y⊗z] C prodF ⊤)
  prod-assoc = record
    { F⇒G = record
      { η = λ _ → assocˡ
      ; commute = λ _ → prod-assoc-commuteˡ
      }
    ; F⇐G = record
      { η = λ _ → assocʳ
      ; commute = λ _ → prod-assoc-commuteʳ
      }
    ; iso = λ _ → record
      { isoˡ = assocʳ∘assocˡ
      ; isoʳ = assocˡ∘assocʳ
      }
    }

{-
p1 : (A × B) × C → A × C
p1 = ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩
   = π₁ ⁂ id

p2 : A × (B × C) → A × C
p2 = ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩
   = id ⁂ π₂

a : (A × B) × C → A × (B × C)
a = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

triangle : p1 = p2 ∘ a
-}

  triL : ∀ (A B C : Obj) → ((A × B) × C) ⇒ (A × C)
  triL _ _ _ = π₁ ⁂ id

  triR : ∀ (A B C : Obj) → (A × (B × C)) ⇒ (A × C)
  triR _ _ _ = id ⁂ π₂

  triT : ∀ (A B C : Obj) → ((A × B) × C) ⇒ (A × (B × C))
  triT _ _ _ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

  .prod-triangle : ∀ {A B C : Obj} → triL A B C ≡ triR A B C ∘ triT A B C
  prod-triangle =
    begin
      π₁ ⁂ id
    ↓⟨ refl ⟩
      ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩
    ↓⟨ ⟨⟩-congʳ identityˡ ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⟩
    ↑⟨ identityˡ ⟩,⟨ commute₂ ⟩
      ⟨ id ∘ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↑⟨ ⁂∘⟨⟩ ⟩
      id ⁂ π₂ ∘ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ∎

  pentNE : (A B C D : Obj) → ((A × B) × (C × D)) ⇒ (A × (B × (C × D)))
  pentNE _ _ _ _ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

  pentNW : (A B C D : Obj) → (((A × B) × C) × D) ⇒ ((A × B) × (C × D))
  pentNW _ _ _ _ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

  pentSE : (A B C D : Obj) → (A × ((B × C) × D)) ⇒ (A × (B × (C × D)))
  pentSE _ _ _ _ = id ⁂ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

  pentSS : (A B C D : Obj) → ((A × (B × C)) × D) ⇒ (A × ((B × C) × D))
  pentSS _ _ _ _ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩

  pentSW : (A B C D : Obj) → (((A × B) × C) × D) ⇒ ((A × (B × C)) × D)
  pentSW _ _ _ _ = ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⁂ id

{-
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ≡
      ⟨ id ∘ π₁ , ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ π₂ ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ∘
      ⟨ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ π₁ , id ∘ π₂ ⟩
-}

  -- There has GOT to be a better way to do this proof.
  .prod-pentagon : ∀ {A B C D : Obj} →
    pentNE A B C D ∘ pentNW A B C D ≡ pentSE A B C D ∘ (pentSS A B C D ∘ pentSW A B C D)
  prod-pentagon =
    begin
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
    ↓⟨ ⟨⟩-congʳ (⟨⟩-congʳ (sym identityˡ)) ⟩∘⟨ ⟨⟩-congʳ (⟨⟩-congʳ (sym identityˡ)) ⟩
      ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩
      ∘
      ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩
    ↓⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩ , (π₂ ⁂ id) ∘ ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩ ⟩
    ↓⟨ assoc ⟩,⟨ ⁂∘⟨⟩ ⟩
      ⟨ π₁ ∘ π₁ ∘ ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩ , ⟨ π₂ ∘ π₁ ∘ π₁ , id ∘ (π₂ ⁂ id) ⟩ ⟩
    ↓⟨ ∘-resp-≡ʳ commute₁ ⟩,⟨ ⟨⟩-congʳ identityˡ ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ⁂ id ⟩ ⟩
    ↓⟨ ⟨⟩-congʳ (⟨⟩-congʳ (⟨⟩-congʳ identityˡ)) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
    ↑⟨ ⟨⟩-congʳ (⟨⟩-congʳ (⟨⟩-congˡ commute₂)) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁
      , ⟨ π₂ ∘ π₁ ∘ π₁
        , ⟨ π₂ ∘ ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ , π₂ ⟩
        ⟩
      ⟩
    ↑⟨ ⟨⟩-congʳ (commute₁ ⟩,⟨ (⟨⟩-congˡ (∘-resp-≡ʳ commute₂))) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁
      , ⟨ π₁ ∘ ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩
        , ⟨ π₂ ∘ π₂ ∘ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩
          , π₂
          ⟩
        ⟩
      ⟩
    ↑⟨ ⟨⟩-congʳ (∘-resp-≡ʳ commute₂ ⟩,⟨ ⟨⟩-congˡ (∘-resp-≡ʳ (∘-resp-≡ʳ commute₁))) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁
      , ⟨ π₁ ∘ π₂ ∘ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩
        , ⟨ π₂ ∘ π₂ ∘ π₁ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
          , π₂
          ⟩
        ⟩
      ⟩
    ↑⟨ ⟨⟩-congʳ ((∘-resp-≡ʳ (∘-resp-≡ʳ commute₁)) ⟩,⟨ (⟨⟩-congˡ (∘-resp-≡ʳ assoc))) ⟩
      ⟨ π₁ ∘ π₁ ∘ π₁
      , ⟨ π₁ ∘ π₂ ∘ π₁ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
        , ⟨ π₂ ∘ (π₂ ∘ π₁) ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
          , π₂
          ⟩
        ⟩
      ⟩
    ↑⟨ commute₁ ⟩,⟨ ((∘-resp-≡ʳ assoc) ⟩,⟨ (assoc ⟩,⟨ commute₂)) ⟩
      ⟨ π₁ ∘ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩
      , ⟨ π₁ ∘ (π₂ ∘ π₁) ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
        , ⟨ (π₂ ∘ π₂ ∘ π₁) ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
          , π₂ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
          ⟩
        ⟩
      ⟩
    ↑⟨ ∘-resp-≡ʳ commute₁ ⟩,⟨ (assoc ⟩,⟨ ⟨⟩∘) ⟩
      ⟨ π₁ ∘ π₁ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
      , ⟨ (π₁ ∘ π₂ ∘ π₁) ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
        , ⟨ π₂ ∘ π₂ ∘ π₁ , π₂ ⟩ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
        ⟩
      ⟩
    ↑⟨ assoc ⟩,⟨ ⟨⟩∘ ⟩
      ⟨ (π₁ ∘ π₁) ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
      , ⟨ π₁ ∘ π₂ ∘ π₁ , ⟨ π₂ ∘ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
      ⟩
    ↑⟨ ⟨⟩∘ ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₁ ∘ π₂ ∘ π₁ , ⟨ π₂ ∘ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⟩
      ∘
      ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
    ↑⟨ (⟨⟩-congʳ (⟨⟩-congʳ ((∘-resp-≡ʳ π₁∘⁂) ⟩,⟨ identityˡ))) ⟩∘⟨ (⟨⟩-congˡ (⟨⟩-congʳ (⟨⟩-congˡ assoc))) ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₁ ∘ π₂ ∘ π₁ , ⟨ π₂ ∘ π₁ ∘ (π₂ ⁂ id) , id ∘ π₂ ⟩ ⟩ ⟩
      ∘
      ⟨ ⟨ π₁ ∘ π₁ ∘ π₁ , ⟨ (π₂ ∘ π₁) ∘ π₁ , π₂ ∘ π₁ ⟩ ⟩ , π₂ ⟩
    ↑⟨ (⟨⟩-congʳ ((∘-resp-≡ʳ π₁∘⁂) ⟩,⟨ (assoc ⟩,⟨ π₂∘⁂))) ⟩∘⟨ (⟨⟩-congˡ (assoc ⟩,⟨ ⟨⟩∘)) ⟩
      ⟨ π₁ ∘ π₁ , ⟨ π₁ ∘ π₁ ∘ (π₂ ⁂ id) , ⟨ (π₂ ∘ π₁) ∘ (π₂ ⁂ id) , π₂ ∘ (π₂ ⁂ id) ⟩ ⟩ ⟩
      ∘
      ⟨ ⟨ (π₁ ∘ π₁) ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ π₁ ⟩ , π₂ ⟩
    ↑⟨ (identityˡ ⟩,⟨ (assoc ⟩,⟨ ⟨⟩∘)) ⟩∘⟨ (⟨⟩∘ ⟩,⟨ identityˡ) ⟩
      ⟨ id ∘ π₁ ∘ π₁ , ⟨ (π₁ ∘ π₁) ∘ (π₂ ⁂ id) , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ (π₂ ⁂ id) ⟩ ⟩
      ∘
      ⟨ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ π₁ , id ∘ π₂ ⟩
    ↑⟨ ∘-resp-≡ˡ (⟨⟩-congʳ ⟨⟩∘) ⟩
      ⟨ id ∘ π₁ ∘ π₁ , ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ∘ (π₂ ⁂ id) ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⁂ id
    ↑⟨ ∘-resp-≡ˡ ⁂∘⟨⟩ ⟩
      ( (id ⁂ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩)
        ∘
        ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩
      )
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⁂ id
    ↑⟨ sym assoc ⟩
      (id ⁂ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩)
      ∘
      ⟨ π₁ ∘ π₁ , π₂ ⁂ id ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⁂ id
    ↑⟨ ∘-resp-≡ʳ (∘-resp-≡ˡ (⟨⟩-congʳ (⟨⟩-congʳ (sym identityˡ)))) ⟩
      (id ⁂ ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩)
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩
      ∘
      ⟨ π₁ ∘ π₁ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ⁂ id
    ∎

  product-monoid : Monoidal C
  product-monoid = record
    { ⊗ = prodF
    ; id = ⊤
    ; identityˡ = left-id
    ; identityʳ = right-id
    ; assoc = prod-assoc
    ; triangle = prod-triangle
    ; pentagon = prod-pentagon
    }

module LiftMonoid {o ℓ e} (C : Category o ℓ e) (D : Category o ℓ e) (m : Monoidal D) where

  open import Categories.NaturalTransformation
  open import Categories.FunctorCategory
  open import Categories.Functor renaming (Functor to _⟶_)
  open import Categories.Functor.Constant

  open NaturalIsomorphism
  open NaturalTransformation
  open Category
  open Functor

  private module C = Category C
  private module D = Category D

  open Data.Product using ( _×_ )

  open Monoidal m

  [C,D] : Category _ _ _
  [C,D] = Functors C D

  ⊗′₀ : (C ⟶ D) × (C ⟶ D) → (C ⟶ D)
  ⊗′₀ (F , G) = record
    { F₀ = λ c → F₀ ⊗ (F₀ F c , F₀ G c)
    ; F₁ = λ A⇒B → F₁ ⊗ (F₁ F A⇒B , F₁ G A⇒B)
    ; identity = trans (F-resp-≡ ⊗ (identity F , identity G)) (identity ⊗)
    ; homomorphism = trans (F-resp-≡ ⊗ (homomorphism F , homomorphism G)) (homomorphism ⊗)
    ; F-resp-≡ = λ H≡J → F-resp-≡ ⊗ (F-resp-≡ F H≡J , F-resp-≡ G H≡J)
    }
    where open D.Equiv

  ⊗′₁ : {G H : Obj (Product [C,D] [C,D])}
     → Product [C,D] [C,D] [ G , H ]
     → [C,D] [ ⊗′₀ G , ⊗′₀ H ]
  ⊗′₁ {G₁ , G₂} {H₁ , H₂} (G₁⇒H₁ , G₂⇒H₂) = record
    { η = λ X → F₁ ⊗ (η G₁⇒H₁ X , η G₂⇒H₂ X)
    ; commute = λ f → trans (sym (homomorphism ⊗))
                     (trans (F-resp-≡ ⊗ (commute G₁⇒H₁ f , commute G₂⇒H₂ f))
                            (homomorphism ⊗))
    }
    where open D.Equiv

  .⊗′-resp-≡ :
      {G H : Obj (Product [C,D] [C,D])}
      {α β : Product [C,D] [C,D] [ G , H ]}
    → Product [C,D] [C,D] [ α ≡ β ]
    → [C,D] [ ⊗′₁ α ≡ ⊗′₁ β ]
  ⊗′-resp-≡ (α₁≡α₂ , β₁≡β₂) = F-resp-≡ ⊗ (α₁≡α₂ , β₁≡β₂)

  ⊗′ : Bifunctor [C,D] [C,D] [C,D]
  ⊗′ = record
    { F₀ = ⊗′₀
    ; F₁ = ⊗′₁
    ; identity = identity ⊗
    ; homomorphism = homomorphism ⊗
    ; F-resp-≡ = λ {G} {H} {α} {β} → ⊗′-resp-≡ {G} {H} {α} {β}
    }

  open import Categories.Monoidal.Helpers
  open MonoidalHelperFunctors

  -- XXX todo: abstract some of this to cut down on repetition

  id⊗x⇒x : NaturalTransformation
    (id⊗x (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  id⊗x⇒x = record
    { η = λ C⟶D → record
      { η       = λ c →   η       (F⇒G (Monoidal.identityˡ m)) (λ _ → F₀ (C⟶D zero) c)
      ; commute = λ f →   commute (F⇒G (Monoidal.identityˡ m)) (λ _ → F₁ (C⟶D zero) f)
      }
    ; commute = λ f {c} → commute (F⇒G (Monoidal.identityˡ m)) (λ _ → η (f zero) c)
    }

  id⊗x⇐x : NaturalTransformation
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (id⊗x (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  id⊗x⇐x = record
    { η = λ C⟶D → record
      { η       = λ c →   η       (F⇐G (Monoidal.identityˡ m)) (λ _ → F₀ (C⟶D zero) c)
      ; commute = λ f →   commute (F⇐G (Monoidal.identityˡ m)) (λ _ → F₁ (C⟶D zero) f)
      }
    ; commute = λ f {c} → commute (F⇐G (Monoidal.identityˡ m)) (λ _ → η (f zero) c)
    }

  id⊗x≅x : NaturalIsomorphism
    (id⊗x (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  id⊗x≅x = record
    { F⇒G = id⊗x⇒x
    ; F⇐G = id⊗x⇐x
    ; iso = λ C⟶D → record
      { isoˡ = λ {c} → Iso.isoˡ (iso (Monoidal.identityˡ m) (λ _ → F₀ (C⟶D zero) c))
      ; isoʳ = λ {c} → Iso.isoʳ (iso (Monoidal.identityˡ m) (λ _ → F₀ (C⟶D zero) c))
      }
    }
    where
      open import Categories.Morphisms D

  x⊗id⇒x : NaturalTransformation
    (x⊗id (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  x⊗id⇒x = record
    { η = λ C⟶D → record
      { η       = λ c →   η       (F⇒G (Monoidal.identityʳ m)) (λ _ → F₀ (C⟶D zero) c)
      ; commute = λ f →   commute (F⇒G (Monoidal.identityʳ m)) (λ _ → F₁ (C⟶D zero) f)
      }
    ; commute = λ f {c} → commute (F⇒G (Monoidal.identityʳ m)) (λ _ → η (f zero) c)
    }

  x⊗id⇐x : NaturalTransformation
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x⊗id (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  x⊗id⇐x = record
    { η = λ C⟶D → record
      { η       = λ c →   η       (F⇐G (Monoidal.identityʳ m)) (λ _ → F₀ (C⟶D zero) c)
      ; commute = λ f →   commute (F⇐G (Monoidal.identityʳ m)) (λ _ → F₁ (C⟶D zero) f)
      }
    ; commute = λ f {c} → commute (F⇐G (Monoidal.identityʳ m)) (λ _ → η (f zero) c)
    }

  x⊗id≅x : NaturalIsomorphism
    (x⊗id (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x    (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  x⊗id≅x = record
    { F⇒G = x⊗id⇒x
    ; F⇐G = x⊗id⇐x
    ; iso = λ C⟶D → record
      { isoˡ = λ {c} → Iso.isoˡ (iso (Monoidal.identityʳ m) (λ _ → F₀ (C⟶D zero) c))
      ; isoʳ = λ {c} → Iso.isoʳ (iso (Monoidal.identityʳ m) (λ _ → F₀ (C⟶D zero) c))
      }
    }
    where
      open import Categories.Morphisms D

  [x⊗y]⊗z⇒x⊗[y⊗z] : NaturalTransformation
    ([x⊗y]⊗z (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x⊗[y⊗z] (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  [x⊗y]⊗z⇒x⊗[y⊗z] = record
    { η = λ C⟶₃D → record
      { η = λ c → η (F⇒G (Monoidal.assoc m)) (λ i → F₀ (C⟶₃D i) c)
      ; commute = λ f → commute (F⇒G (Monoidal.assoc m)) (λ i → F₁ (C⟶₃D i) f)
      }
    ; commute = λ f {c} → commute (F⇒G (Monoidal.assoc m)) (λ i → η (f i) c)
    }

  [x⊗y]⊗z⇐x⊗[y⊗z] : NaturalTransformation
    (x⊗[y⊗z] (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    ([x⊗y]⊗z (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  [x⊗y]⊗z⇐x⊗[y⊗z] = record
    { η = λ C⟶₃D → record
      { η = λ c → η (F⇐G (Monoidal.assoc m)) (λ i → F₀ (C⟶₃D i) c)
      ; commute = λ f → commute (F⇐G (Monoidal.assoc m)) (λ i → F₁ (C⟶₃D i) f)
      }
    ; commute = λ f {c} → commute (F⇐G (Monoidal.assoc m)) (λ i → η (f i) c)
    }

  [x⊗y]⊗z≅x⊗[y⊗z] : NaturalIsomorphism
    ([x⊗y]⊗z (Functors C D) ⊗′ (Constant (Monoidal.id m)))
    (x⊗[y⊗z] (Functors C D) ⊗′ (Constant (Monoidal.id m)))
  [x⊗y]⊗z≅x⊗[y⊗z] = record
    { F⇒G = [x⊗y]⊗z⇒x⊗[y⊗z]
    ; F⇐G = [x⊗y]⊗z⇐x⊗[y⊗z]
    ; iso = λ C⟶₃D → record
      { isoˡ = λ {c} → Iso.isoˡ (iso (Monoidal.assoc m) (λ i → F₀ (C⟶₃D i) c))
      ; isoʳ = λ {c} → Iso.isoʳ (iso (Monoidal.assoc m) (λ i → F₀ (C⟶₃D i) c))
      }
    }
    where
      open import Categories.Morphisms D

  lifted-monoid : Monoidal (Functors C D)
  lifted-monoid = {!!}
    -- record
    -- { ⊗ = ⊗′
    -- ; id = Constant (Monoidal.id m)
    -- ; identityˡ = id⊗x≅x
    -- ; identityʳ = x⊗id≅x
    -- ; assoc = [x⊗y]⊗z≅x⊗[y⊗z]
    -- ; triangle = {!!}
    -- ; pentagon = {!!}
    -- }
