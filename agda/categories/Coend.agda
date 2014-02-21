open import Categories.Category

module Categories.Coend {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {V : Category o′ ℓ′ e′} where
private
  module C = Category C
  module V = Category V
open import Categories.Bifunctor using (Bifunctor; Functor; module Functor)
open import Categories.DinaturalTransformation
open import Categories.Functor.Constant
open import Level
open import Categories.Morphisms V
open import Categories.Square
open import Data.Product

record Coend-data (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    E : V.Obj
    π : DinaturalTransformation {C = C} F (Constant E)

  module π = DinaturalTransformation π
  open π using (α)
  π∘_ : ∀ {Q} → E V.⇒ Q → Coend-data F
  π∘_ {Q} g = record { π = record { α = λ c → g ∘ α c ; commute = λ {c c′} f →
           begin
              id ∘ (g ∘ α c′) ∘ F.F₁ (C.id , f) 
           ↓⟨ identityˡ ⟩ 
              (g ∘ α c′) ∘ F.F₁ (C.id , f) 
           ↓⟨ assoc ⟩ 
              g ∘ (α c′ ∘ F.F₁ (C.id , f))
           ↓⟨ ∘-resp-≡ʳ (Equiv.trans (Equiv.trans (Equiv.sym identityˡ) (π.commute f)) (identityˡ)) ⟩
              g ∘ (α c ∘ F.F₁ (f , C.id))
           ↓⟨ Equiv.sym assoc ⟩
              (g ∘ α c) ∘ F.F₁ (f , C.id)
            ↓⟨ Equiv.sym identityˡ ⟩ 
             id ∘ (g ∘ α c) ∘ F.F₁ (f , C.id) 
           ∎ } ;
           E = Q } -- Agda is somehow super-smart and can infer this!!  Unification rules!
   where
     -- open AUReasoning V
     module F = Functor F 
     open V
     open HomReasoning
 {- 
  .commute : ∀ {a b} (f : a C.⇒ b) -> Functor.F₁ F (f , C.id) V.∘ α b V.≡ Functor.F₁ F (C.id , f) V.∘ α a
  commute {c} {c′} f = begin
            F.F₁ (f , C.id) ∙ α c′      ↓⟨ Equiv.refl ⟩
            F.F₁ (f , C.id) ∙ α c′ ∙ ID ↓≡⟨ π.commute f ⟩ 
            F.F₁ (C.id , f) ∙ α c  ∙ ID ↓⟨ Equiv.refl ⟩ 
            F.F₁ (C.id , f) ∙ α c       ∎
    where 
      open AUReasoning V
      module F = Functor F 
      open V
-}

open DinaturalTransformation using (α)


record Coend (F : Bifunctor C.op C V) : Set (o ⊔ ℓ ⊔ e ⊔ o′ ⊔ ℓ′ ⊔ e′) where
  field
    Data : Coend-data F

  open Coend-data Data

  IsUni : (Q : Coend-data F) → (u : E V.⇒ Coend-data.E Q) → Set _
  IsUni Q u = ∀ c → u V.∘ α π c V.≡ α (Coend-data.π Q) c

  field
    universal : (Q : Coend-data F) →  V [ E , Coend-data.E Q ]

    .π[c]∘universal≡δ[c] : {Q : Coend-data F} → IsUni Q (universal Q)

    .universal-unique : {Q : Coend-data F} → ∀ u → IsUni Q u → u V.≡ universal Q

  .eta-rule : universal Data V.≡ V.id
  eta-rule = begin universal Data ↑⟨ universal-unique {Data} V.id (λ c → V.identityˡ) ⟩ 
                   V.id           ∎
   where
    open V.HomReasoning

{-
  .π-mono : ∀ {Q} (g₁ g₂ : Q V.⇒ E) → (∀ c → α π c V.∘ g₁ V.≡ α π c V.∘ g₂) → g₁ V.≡ g₂
  π-mono {Q} g₁ g₂ π∘g₁≡π∘g₂ = begin 
     g₁                ↓⟨ universal-unique {π∘ g₁} g₁ (λ c → V.Equiv.refl) ⟩ 
     universal (π∘ g₁) ↑⟨ universal-unique {π∘ g₁} g₂ (λ c → V.Equiv.sym (π∘g₁≡π∘g₂ c)) ⟩ 
     g₂                ∎
    where
     open V.HomReasoning
-}
  open Coend-data Data public

--  This is a scary proof; of course, we just need its DUAL, but that is ever so easy to say...
open import Data.Product
open import Categories.Product
open import Categories.FunctorCategory
import Categories.NaturalTransformation as NT
open NT.NaturalTransformation using (η)

postulate
  coendF : ∀ {o ℓ e} {A : Category o ℓ e}(F : Functor A (Functors (Product C.op C) V)) 
        → (∀ a → Coend (Functor.F₀ F a)) → Functor A V
{-
coendF {A = A} F mkc = record
  { F₀ = λ a → Coend.E (mkc a)
  ; F₁ = λ {a b} → F₁ {a} {b}
  }
  where
  module A = Category A
  module F = Functor F
  open V
  -- open AUReasoning V
  F₁ = λ {a b} f → Coend.universal (mkc a) (record { E = _; π = (Coend.π (mkc b)) ∘> (F.F₁ f) })

-}

{-
endF {A = A} F mke = record {
                   F₀ = λ a → End.E (mke a);
                   F₁ = λ {a b} → F₁ {a} {b} ;
                   identity = λ {a} → V.Equiv.sym (End.universal-unique (mke a) V.id (λ c → 
                     begin α (End.π (mke a)) c ∙ ID                    ↓⟨ Equiv.refl ⟩ 
                           ID ∙ α (End.π (mke a)) c                    ↑≡⟨ ∘-resp-≡ˡ F.identity ⟩ 
                           η (F.F₁ A.id) (c , c) ∙ α (End.π (mke a)) c ∎)) ;
                   homomorphism = λ {X Y Z f g} → V.Equiv.sym (End.universal-unique (mke Z) _ (λ c → 
                       begin α (End.π (mke Z)) c ∙ F₁ g ∙ F₁ f 
                                   ↑⟨ Equiv.refl ⟩ 
                             (α (End.π (mke Z)) c ∙ F₁ g) ∙ F₁ f
                                   ↓≡⟨ ∘-resp-≡ˡ (End.π[c]∘universal≡δ[c] (mke Z) {record {π = F.F₁ g <∘ End.π (mke Y)}} c) ⟩ 
                             (η (F.F₁ g) (c , c) ∙ α (End.π (mke Y)) c) ∙ F₁ f 
                                   ↓⟨ Equiv.refl ⟩ 
                             η (F.F₁ g) (c , c) ∙ α (End.π (mke Y)) c ∙ F₁ f
                                   ↓≡⟨ ∘-resp-≡ʳ (End.π[c]∘universal≡δ[c] (mke Y) {record {π = F.F₁ f <∘ End.π (mke X)}} c) ⟩ 
                             η (F.F₁ g) (c , c) ∙ η (F.F₁ f) (c , c) ∙ α (End.π (mke X)) c 
                                   ↑⟨ Equiv.refl ⟩ 
                             (η (F.F₁ g) (c , c) ∙ η (F.F₁ f) (c , c)) ∙ α (End.π (mke X)) c 
                                   ↑≡⟨ ∘-resp-≡ˡ F.homomorphism  ⟩
                             η (F.F₁ (A [ g ∘ f ])) (c , c) ∙ α (End.π (mke X)) c 
                                                                                   ∎));
                   F-resp-≡ = λ {a b f g} f≡g → End.universal-unique (mke b) _ (λ c → 
                       begin α (End.π (mke b)) c ∙ F₁ f               ↓≡⟨ End.π[c]∘universal≡δ[c] (mke b) c ⟩ 
                             η (F.F₁ f) (c , c) ∙ α (End.π (mke a)) c ↓≡⟨ ∘-resp-≡ˡ (F.F-resp-≡ f≡g) ⟩ 
                             η (F.F₁ g) (c , c) ∙ α (End.π (mke a)) c ∎)} 
 where
  module A = Category A
  module F = Functor F
  open V
  open AUReasoning V
  F₁ = λ {a b} f → End.universal (mke b) (record { E = _; π = (F.F₁ f) <∘ (End.π (mke a)) })
-}
