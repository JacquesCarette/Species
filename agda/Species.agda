{-# OPTIONS --without-K #-}

open import HoTT
open import GCBP

module Species where

--------------------------------------------------
-- Lemmas about univalence

-- The univalence axiom applied to the identity equivalence is reflexivity.
ua-id : {A : Set} → ua (ide A) == idp
ua-id = ua-η idp

-- Don't actually need this one, but it's the way the book presents
-- the beta-rule for univalence, so it's nice to see we can derive it
-- from the way the Agda library encodes things
transport-ua : ∀ {A B : Set} (e : A ≃ B) (x : A) → transport (λ X → X) (ua e) x == –> e x
transport-ua e x
  = equiv-induction
      (λ e₁ → transport (λ X → X) (ua e₁) == –> e₁)
      (λ _ → ua-id |in-ctx (coe ∘ ap (λ X → X)))
      e
    |in-ctx (λ f → f x)

lem-transport-path-hom : ∀ {A B : Set} (e : A == B) {X : Set} (f : X == A) → transport (_==_ X) e f == f ∙ e
lem-transport-path-hom idp idp = idp

ideL : ∀ {A B : Set} (e : A ≃ B) → ide B ∘e e == e
ideL = equiv-induction (λ {A} {B} e₁ → ide B ∘e e₁ == e₁) (λ A → idp)

ideR : ∀ {A B : Set} (e : A ≃ B) → e ∘e ide A == e
ideR = equiv-induction (λ {A} e → e ∘e ide A == e) (λ _ → idp)

equiv-cancelR : ∀ {A B : Set} (f : A ≃ B) (e : B ≃ B) → (e ∘e f == f) → (e == (ide B))
equiv-cancelR =
  equiv-induction
    (λ {A} {B} f → (e : B ≃ B) → (e ∘e f == f) → (e == (ide B)))
    (λ B e x →
      e
          =⟨ ! (ideR e) ⟩
      e ∘e ide B
          =⟨ x ⟩
      ide B
          ∎
    )

transport-by-ua-is-comp : ∀ {A B : Set} (e : A ≃ B) {X : Set} (f : X ≃ A) → transport (λ Z → X ≃ Z) (ua e) f == e ∘e f
transport-by-ua-is-comp e = equiv-induction
                              (λ {A} {B} e₁ →
                                 {X : Set} (f : X ≃ A) →
                                 transport (λ Z → X ≃ Z) (ua e₁) f == e₁ ∘e f)
                              (λ A {X} f →
                                 transport (_≃_ X) (ua (ide A)) f
                                     =⟨ ap (λ p → transport (_≃_ X) p f) ua-id ⟩
                                 f
                                     =⟨ ! (ideL f) ⟩
                                 ide _ ∘e f
                                     ∎
                              )
                              e

-- Fin -----------------------------------------------------

data Fin : ℕ → Set where
  fO : {n : ℕ} → Fin (S n)
  fS : {n : ℕ} → Fin n → Fin (S n)

fO-elim : ∀ {i} {A : Fin 0 → Type i} → (x : Fin 0) → A x
fO-elim ()

⊥≃Fin0 : ⊥ ≃ Fin 0
⊥≃Fin0 = equiv Empty-elim fO-elim fO-elim Empty-elim

Fin1=fO : (a : Fin 1) → fO == a
Fin1=fO fO = idp
Fin1=fO (fS ())

⊤≃Fin1 : ⊤ ≃ Fin 1
⊤≃Fin1 = equiv (cst fO) (cst unit) Fin1=fO (λ {unit → idp})

FinSm≃Finm+⊤ : (m : ℕ) → Fin (S m) ≃ (Coprod (Fin m) ⊤)
FinSm≃Finm+⊤ m = equiv f g fg gf
  where
    f : ∀ {m : ℕ} → Fin (S m) → (Coprod (Fin m) ⊤)
    f fO     = inr unit
    f (fS x) = inl x
    g : ∀ {m : ℕ} → (Coprod (Fin m) ⊤) → Fin (S m)
    g (inr _) = fO
    g (inl x) = fS x
    fg : ∀ {m : ℕ} → (b : Coprod (Fin m) ⊤) → (f (g b) == b)
    fg (inr unit) = idp
    fg (inl x) = idp
    gf : ∀ {m : ℕ} → (b : Fin (S m)) → (g (f b) == b)
    gf fO = idp
    gf (fS x) = idp

Fin≃-= : (m n : ℕ) → (Fin m ≃ Fin n) → (m == n)
Fin≃-= O O e = idp
Fin≃-= O (S n) e = fO-elim (<– e fO)
Fin≃-= (S m) O e = fO-elim (–> e fO)
Fin≃-= (S m) (S n) e = ap S (Fin≃-= m n (gcbp (FinSm≃Finm+⊤ n ∘e e ∘e FinSm≃Finm+⊤ m ⁻¹) (ide ⊤)))

-- Codes for labels ----------------------------------------

-- We use a set of codes for "allowed" label types, to get around
-- problems with impredicativity.  The specific codes used are not
-- important; in principle we can add codes for as many things as we
-- like.  The important point is that we cannot use a set of species
-- structures as labels.

data Code : Set where
  CFin  : ℕ → Code
  CSum  : Code → Code → Code
  CProd : Code → Code → Code

⟦_⟧ : Code → Set
⟦ CFin n ⟧ = Fin n
⟦ CSum  c₁ c₂ ⟧ = Coprod ⟦ c₁ ⟧ ⟦ c₂ ⟧
⟦ CProd c₁ c₂ ⟧ = ⟦ c₁ ⟧ × ⟦ c₂ ⟧

-- We require the property that two distinct codes never map to the
-- same interpretation.  This would be straightforward but tedious to
-- prove by induction on codes; for now we simply postulate it as an
-- axiom.
postulate Codes-unique : {c₁ c₂ : Code} → (⟦ c₁ ⟧ == ⟦ c₂ ⟧) → (c₁ == c₂)

-- FinSet --------------------------------------------------

-- syntax Σ A (λ a → B) = Σ[ a ∈ A ] B

module FinSet₁ where

  IsFinite : Code → Set
  IsFinite A = Σ ℕ (λ n → Fin n ≃ ⟦ A ⟧)

  FinSet : Set
  FinSet = Σ Code IsFinite

  CodeOf : FinSet → Code
  CodeOf ( C , _ ) = C

  -- \|
  ∣_∣ : FinSet → ℕ
  ∣ _ , (n , _) ∣ = n

  -- \clL , \clR
  ⌊_⌋ : FinSet → Set
  ⌊ A , _ ⌋ = ⟦ A ⟧

  FinPf : (L : FinSet) → (Fin ∣ L ∣ ≃ ⌊ L ⌋)
  FinPf ( _ , (_ , p)) = p

  ⌈_⌉ : ℕ → FinSet
  ⌈ n ⌉ = CFin n , (n , ide (Fin n))

--------------------------------------------------
-- Characterizing equalities between FinSets

  FinSet-eq-type : FinSet → FinSet → Set
  FinSet-eq-type L₁ L₂
    = Σ (⌊ L₁ ⌋ ≃ ⌊ L₂ ⌋) (λ p →
        Σ (∣ L₁ ∣ == ∣ L₂ ∣)  (λ q →
          (transport (λ S₁ → Fin ∣ L₂ ∣ ≃ S₁) (ua p)
            (transport (λ sz → Fin sz ≃ ⌊ L₁ ⌋) q (FinPf L₁)) == FinPf L₂)
        )
      )

  FinSet-equiv→ : (L₁ L₂ : FinSet) → (L₁ == L₂) → FinSet-eq-type L₁ L₂
  FinSet-equiv→ L₁ L₂ L₁==L₂ = J (λ L₁' _ → FinSet-eq-type L₁ L₁') (ide ⌊ L₁ ⌋ , (idp , f)) L₁==L₂
    where
      f : coe
            (ap (λ S₁ → (Fin ∣ L₁ ∣ ≃ S₁))
              (ua (ide _))
            )
          (FinPf L₁)
          ==
          FinPf L₁
      f with L₁
      ... | (L₁C , (L₁n , L₁F)) = ua-id |in-ctx (λ a → coe (ap (λ S₁ → (Fin L₁n ≃ S₁)) a) L₁F)

  FinSet-equiv← : (L₁ L₂ : FinSet) → FinSet-eq-type L₁ L₂ → (L₁ == L₂)
  FinSet-equiv← (L₁C , (L₁n , L₁F)) (L₂C , (L₂n , L₂F)) (L₁C≃L₂C , (L₁n=L₂n , L₁F=L₂F))
    = pair= (Codes-unique (ua L₁C≃L₂C)) {!!}

  FinSet-equiv : (L₁ L₂ : FinSet) → (L₁ == L₂) ≃ FinSet-eq-type L₁ L₂
  FinSet-equiv L₁ L₂ = equiv (FinSet-equiv→ L₁ L₂) (FinSet-equiv← L₁ L₂) f {!!}
    where
      f : _
      f with L₁ | L₂
      ... | (L₁C , (L₁n , L₁F)) | (L₂C , (L₂n , L₂F)) = {!!}

  -- This, on the other hand, is false: the finite proofs may not match.
  -- lift-⌊⌋-equiv : ∀ {L₁ L₂ : FinSet} → (⌊ L₁ ⌋ ≃ ⌊ L₂ ⌋) → (L₁ == L₂)

  UIP-ℕ : (n : ℕ) → (p : n == n) → (p == idp)
  UIP-ℕ n p = fst $ ℕ-is-set n n p idp

  -- There are no nontrivial automorphisms on FinSets!
  FinSet-no-auto : (L : FinSet) → (p : L == L) → (p == idp)
  FinSet-no-auto L p with FinSet-equiv→ L L p
  FinSet-no-auto (C , (n , F)) p | C≃C , (n=n , F=F) = {!!}
    where

      -- most of the interesting work is done now, just needs to be
      -- put back together to conclude p == idp
      compPf : C≃C ∘e F == F
      compPf =
        C≃C ∘e F
            =⟨ ! (transport-by-ua-is-comp C≃C F) ⟩
        transport (_≃_ (Fin n)) (ua C≃C) F
            =⟨ transport
                 (λ p₁ → transport (_≃_ (Fin n)) (ua C≃C) (transport (λ sz → Fin sz ≃ ⟦ C ⟧) p₁ F) == F)
                 (UIP-ℕ n n=n)
                 F=F
             ⟩
        F ∎

      C≃C-is-id : C≃C == ide ⟦ C ⟧
      C≃C-is-id = equiv-cancelR F C≃C compPf

-- FinSets: another try ------------------------------------

module FinSet₂ where

  IsFinite : Code → Set
  IsFinite A = Σ ℕ (λ n → Trunc ⟨-1⟩ (Fin n ≃ ⟦ A ⟧))

  FinSet : Set
  FinSet = Σ Code IsFinite

  CodeOf : FinSet → Code
  CodeOf ( C , _ ) = C

  -- \|
  ∣_∣ : FinSet → ℕ
  ∣ _ , (n , _) ∣ = n

  -- \clL , \clR
  ⌊_⌋ : FinSet → Set
  ⌊ A , _ ⌋ = ⟦ A ⟧

  FinPf : (L : FinSet) → Trunc ⟨-1⟩ (Fin ∣ L ∣ ≃ ⌊ L ⌋)
  FinPf ( _ , (_ , p)) = p

  ⌈_⌉ : ℕ → FinSet
  ⌈ n ⌉ = CFin n , (n , [ ide (Fin n) ])

  lift-⌊⌋-equiv' : (⟦L₁C⟧ ⟦L₂C⟧ : Set) (e : ⟦L₁C⟧ ≃ ⟦L₂C⟧) (L₁n L₂n : ℕ)
                   (L₁F : Trunc ⟨-1⟩ (Fin L₁n ≃ ⟦L₁C⟧))
                   (L₂F : Trunc ⟨-1⟩ (Fin L₂n ≃ ⟦L₂C⟧))
                 → (Σ (L₁n == L₂n)
                      (λ p → transport (λ n → Trunc ⟨-1⟩ (Fin n ≃ ⟦L₂C⟧)) p (transport (λ c → Trunc ⟨-1⟩ (Fin L₁n ≃ c)) (ua e) L₁F) == L₂F)
                   )
  lift-⌊⌋-equiv' ⟦L₁C⟧ ⟦L₂C⟧ = equiv-induction
                                 (λ {A} {B} e →
                                    (L₁n L₂n : ℕ) (L₁F : Trunc ⟨-1⟩ (Fin L₁n ≃ A))
                                    (L₂F : Trunc ⟨-1⟩ (Fin L₂n ≃ B)) →
                                    Σ (L₁n == L₂n)
                                    (λ p →
                                       transport (λ n → Trunc ⟨-1⟩ (Fin n ≃ B)) p
                                       (transport (λ c → Trunc ⟨-1⟩ (Fin L₁n ≃ c)) (ua e) L₁F)
                                       == L₂F))
                                 (λ S L₁n L₂n L₁F L₂F →
                                    (Trunc-elim (λ _ → ℕ-is-set L₁n L₂n) (λ eqv₁ →
                                    (Trunc-elim (λ _ → ℕ-is-set L₁n L₂n) (λ eqv₂ →
                                       Fin≃-= L₁n L₂n (eqv₂ ⁻¹ ∘e eqv₁))
                                    L₂F)) L₁F)
                                 , fst (Trunc-level {n = ⟨-1⟩} {A = Fin L₂n ≃ S} _ _)
                                 )

  -- Now that we are using propositional truncation, this should actually be true
  lift-⌊⌋-equiv : (L₁ L₂ : FinSet) → (⌊ L₁ ⌋ ≃ ⌊ L₂ ⌋) → (L₁ == L₂)
  lift-⌊⌋-equiv (L₁C , (L₁n , L₁F)) (L₂C , (L₂n , L₂F)) iso
    with lift-⌊⌋-equiv' ⟦ L₁C ⟧ ⟦ L₂C ⟧ iso L₁n L₂n L₁F L₂F
  ... | (eqn , eqF) = pair= (Codes-unique (ua iso)) {!!}

  ⊥F : FinSet
  ⊥F = (CFin 0) , (0 , [ ide _ ])

  ⊤F : FinSet
  ⊤F = (CFin 1) , (1 , [ ide _ ])

open FinSet₂

-- Species -------------------------------------------------

Species : Set₁
Species = FinSet → Set

relabel : ∀ {F : Species} {L₁ L₂ : FinSet} → (L₁ == L₂) → F L₁ → F L₂
relabel {F} = transport F

-- Species algebra -----------------------------------------

-- Zero --------------------------------

Zero : Species
Zero _ = ⊥

-- One ---------------------------------

One : Species
One L = ⊥ ≃ ⌊ L ⌋

one : One ⌈ 0 ⌉
one = ⊥≃Fin0

-- X -----------------------------------

X : Species
X L = ⊤ ≃ ⌊ L ⌋

x : X ⌈ 1 ⌉
x = ⊤≃Fin1

-- Sum ---------------------------------

_⊎_ : {i j : ULevel} → Set i → Set j → Set (lmax j i)
_⊎_ = Coprod
-- \u+

⊎-assocL : ∀ {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
⊎-assocL (inl x) = inl (inl x)
⊎-assocL (inr (inl x)) = inl (inr x)
⊎-assocL (inr (inr x)) = inr x

⊎-assocR : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
⊎-assocR (inl (inl x)) = inl x
⊎-assocR (inl (inr x)) = inr (inl x)
⊎-assocR (inr x) = inr (inr x)

⊎-assoc : ∀ {A B C : Set} → ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
⊎-assoc = equiv ⊎-assocR ⊎-assocL ⊎-RL ⊎-LR
  where
    ⊎-RL : ∀ {A B C : Set} → (b : A ⊎ (B ⊎ C)) → ⊎-assocR (⊎-assocL b) == b
    ⊎-RL (inl x) = idp
    ⊎-RL (inr (inl x)) = idp
    ⊎-RL (inr (inr x)) = idp

    ⊎-LR : ∀ {A B C : Set} → (b : (A ⊎ B) ⊎ C) → ⊎-assocL (⊎-assocR b) == b
    ⊎-LR (inl (inl x)) = idp
    ⊎-LR (inl (inr x)) = idp
    ⊎-LR (inr x) = idp

⊎-idL : ∀ {A : Set} → (⊥ ⊎ A) ≃ A
⊎-idL = equiv ⊎-projR inr (λ _ → idp) ⊎-inrProjR
  where
    ⊎-projR : ∀ {A : Set} → (⊥ ⊎ A) → A
    ⊎-projR (inl ())
    ⊎-projR (inr a) = a
    ⊎-inrProjR : ∀ {A : Set} → (a : ⊥ ⊎ A) → inr (⊎-projR a) == a
    ⊎-inrProjR (inl ())
    ⊎-inrProjR (inr x) = idp

⊎-idR : ∀ {A : Set} → (A ⊎ ⊥) ≃ A
⊎-idR = equiv ⊎-projL inl (λ _ → idp) ⊎-inlProjL
  where
    ⊎-projL : ∀ {A : Set} → (A ⊎ ⊥) → A
    ⊎-projL (inl a) = a
    ⊎-projL (inr ())
    ⊎-inlProjL : ∀ {A : Set} → (a : A ⊎ ⊥) → inl (⊎-projL a) == a
    ⊎-inlProjL (inl x) = idp
    ⊎-inlProjL (inr ())

⊎-≃ : ∀ {A₁ B₁ A₂ B₂ : Set} → (A₁ ≃ B₁) → (A₂ ≃ B₂) → ((A₁ ⊎ A₂) ≃ (B₁ ⊎ B₂))
⊎-≃ e₁ e₂ = equiv (λ { (inl a₁) → inl (–> e₁ a₁) ; (inr a₂) → inr (–> e₂ a₂) })
                  (λ {(inl b₁) → inl (<– e₁ b₁); (inr b₂) → inr (<– e₂ b₂)})
                  (λ {(inl b₁) → ap inl (<–-inv-r e₁ b₁); (inr b₂) → ap inr (<–-inv-r e₂ b₂)})
                  (λ {(inl a₁) → ap inl (<–-inv-l e₁ a₁); (inr a₂) → ap inr (<–-inv-l e₂ a₂)})

_⊞_ : Species → Species → Species
(F ⊞ G) L = F L ⊎ G L
-- \b+

⊞inl : ∀ {F G : Species} {L : FinSet} → F L → (F ⊞ G) L
⊞inl = inl

⊞inr : ∀ {F G : Species} {L : FinSet} → G L → (F ⊞ G) L
⊞inr = inr

⊞-assoc : ∀ {F G H : Species} → ((F ⊞ G) ⊞ H) == (F ⊞ (G ⊞ H))
⊞-assoc = λ= (λ _ → ua ⊎-assoc)

⊞-idL : ∀ {F : Species} → (Zero ⊞ F) == F
⊞-idL = λ= (λ _ → ua ⊎-idL)

⊞-idR : ∀ {F : Species} → (F ⊞ Zero) == F
⊞-idR = λ= (λ _ → ua ⊎-idR)

-- Product -----------------------------

-- \b.
_⊡_ : Species → Species → Species
(F ⊡ G) L = Σ FinSet (λ L₁ → Σ FinSet (λ L₂ →
              ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (F L₁ × G L₂)
            ))

⊡pair : ∀ {F G : Species} {L₁ L₂ L : FinSet}
       → ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋)
       → F L₁ → G L₂ → (F ⊡ G) L
⊡pair {_} {_} {L₁} {L₂} iso f g
  = L₁ , (L₂ , (iso , (f , g)))

⊡-idL : ∀ {F : Species} {L : FinSet} → (One ⊡ F) L ≃ F L
⊡-idL {F} {L} =
  (equiv
    (f F L)
    (g F L)
    (fg F L)
    (gf F L)
  )
  where
    f : (F : Species) → (L : FinSet) → (One ⊡ F) L → F L
    f _ L (L₁ , (L₂ , (iso , (⊥≃L₁ , FL₂)))) = relabel (lift-⌊⌋-equiv L₂ L (⌊ L₂ ⌋ ≃⟨ ⊎-idL ⁻¹ ⟩ ⊥ ⊎ ⌊ L₂ ⌋ ≃⟨ ⊎-≃ ⊥≃L₁ (ide _) ⟩ ⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋ ≃⟨ iso ⟩ ⌊ L ⌋ ≃∎)) FL₂
    g : (F : Species) → (L : FinSet) → F L → (One ⊡ F) L
    g _ L FL = ⊥F , (L , ( Fin 0 ⊎ ⌊ L ⌋
                               ≃⟨ ⊎-≃ (⊥≃Fin0 ⁻¹) (ide _) ⟩
                           ⊥ ⊎ ⌊ L ⌋
                               ≃⟨ ⊎-idL ⟩
                           ⌊ L ⌋
                               ≃∎
                         , (⊥≃Fin0 , FL)))
    fg : (F : Species) → (L : FinSet) → (x : F L) → (f F L (g F L x) == x)
    fg _ L FL = {!!}
    gf : (F : Species) → (L : FinSet) → (x : (One ⊡ F) L) → (g F L (f F L x) == x)
    gf = {!!}

{-
      (One ⊡ F) == F
λ= :: ∀ L : FinSet . (One ⊡ F) L == F L
ua :: ∀ L : FinSet . (One ⊡ F) L ≃  F L
ua :: ∀ L : FinSet . ( Σ (L₁ L₂ : FinSet). ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (One L₁ × F L₂) ) ≃ F L
   :: ∀ L : FinSet . ( Σ (L₁ L₂ : FinSet). ((⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋) ≃ ⌊ L ⌋) × (⊥ ≃ ⌊ L₁ ⌋ × F L₂) ) ≃ F L

      ⌊ L ⌋ ≃ ⌊ L₁ ⌋ ⊎ ⌊ L₂ ⌋ ≃ ⊥ ⊎ ⌊ L₂ ⌋ ≃ ⌊ L₂ ⌋

      We can conclude from ⌊ L ⌋ ≃ ⌊ L₂ ⌋ that L == L₂; then relabel.

-}
