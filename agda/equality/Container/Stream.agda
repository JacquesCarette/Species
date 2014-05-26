------------------------------------------------------------------------
-- The stream container
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Container.Stream where

open import Container
open import Container.List as L hiding (_∷_; _++_; Any-∷; Any-++)
open import Equality.Propositional
open import Logical-equivalence using (_⇔_)
open import Prelude hiding (id; List; []; _∷_; _++_; head; tail)

open import Bijection equality-with-J using (_↔_; module _↔_)
open import Function-universe equality-with-J hiding (_∘_)

------------------------------------------------------------------------
-- Streams

Stream : Container lzero
Stream = ⊤ ▷ const ℕ

------------------------------------------------------------------------
-- Operations

-- Cons.

infixr 5 _∷_

_∷_ : {A : Set} → A → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
x ∷ (tt , lkup) = tt , λ { zero → x; (suc n) → lkup n }

-- The head of a stream.

head : {A : Set} → ⟦ Stream ⟧ A → A
head (tt , lkup) = lkup 0

-- The tail of a stream.

tail : {A : Set} → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
tail (tt , lkup) = (tt , lkup ∘ suc)

-- Appending a list to a stream.

infixr 5 _++_

_++_ : {A : Set} → ⟦ List ⟧ A → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
xs ++ ys = fold ys (λ z _ zs → z ∷ zs) xs

-- Taking the first n elements from a stream.

take : {A : Set} → ℕ → ⟦ Stream ⟧ A → ⟦ List ⟧ A
take zero    xs = []
take (suc n) xs = L._∷_ (head xs) (take n (tail xs))

-- Dropping the first n elements from a stream.

drop : {A : Set} → ℕ → ⟦ Stream ⟧ A → ⟦ Stream ⟧ A
drop zero    xs = xs
drop (suc n) xs = drop n (tail xs)

------------------------------------------------------------------------
-- Any lemmas

-- Any lemma for head/tail.

Any-head-tail : ∀ {A : Set} (P : A → Set) {xs} →
                Any P xs ↔ P (head xs) ⊎ Any P (tail xs)
Any-head-tail P = record
  { surjection = record
    { logical-equivalence = record
      { to   = λ { (zero  , p) → inj₁ p
                 ; (suc n , p) → inj₂ (n , p)
                 }
      ; from = λ { (inj₁ p)       → (zero , p)
                 ; (inj₂ (n , p)) → (suc n , p)
                 }
      }
    ; right-inverse-of = λ { (inj₁ p)       → refl
                           ; (inj₂ (n , p)) → refl
                           }
    }
  ; left-inverse-of = λ { (zero  , p) → refl
                        ; (suc n , p) → refl
                        }
  }

-- Any lemma for cons.

Any-∷ : ∀ {A : Set} (P : A → Set) {x xs} →
        Any P (x ∷ xs) ↔ P x ⊎ Any P xs
Any-∷ P = Any-head-tail P

-- Any lemma for append.
--
-- (TODO: Generalise. The definitions of _++_ and Any-++ in this
-- module are almost identical to those in Container.List.)

Any-++ : ∀ {A : Set} (P : A → Set) (xs : ⟦ List ⟧ A) ys →
         Any P (xs ++ ys) ↔ Any P xs ⊎ Any P ys
Any-++ P xs ys = fold-lemma
  (λ xs xs++ys → Any P xs++ys ↔ Any P xs ⊎ Any P ys)

  (λ us vs us≈vs us++ys hyp →
    Any P us++ys         ↔⟨ hyp ⟩
    Any P us ⊎ Any P ys  ↔⟨ _⇔_.to (∼⇔∼″ us vs) us≈vs P ⊎-cong id ⟩
    Any P vs ⊎ Any P ys  □)

  (Any P ys             ↔⟨ inverse ⊎-left-identity ⟩
   ⊥ ⊎ Any P ys         ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
   Any P [] ⊎ Any P ys  □)

  (λ x xs xs++ys ih →
     Any P (x ∷ xs++ys)             ↔⟨ Any-∷ P ⟩
     P x ⊎ Any P xs++ys             ↔⟨ id ⊎-cong ih ⟩
     P x ⊎ Any P xs ⊎ Any P ys      ↔⟨ ⊎-assoc ⟩
     (P x ⊎ Any P xs) ⊎ Any P ys    ↔⟨ inverse $ L.Any-∷ P ⊎-cong id ⟩
     Any P (L._∷_ x xs) ⊎ Any P ys  □)

  xs

-- Any lemma for take/drop.

Any-take-drop : ∀ {A : Set} (P : A → Set) n {xs} →
                Any P xs ↔ Any P (take n xs) ⊎ Any P (drop n xs)
Any-take-drop P zero {xs} =
  Any P xs             ↔⟨ inverse ⊎-left-identity ⟩
  ⊥        ⊎ Any P xs  ↔⟨ inverse (Any-[] P) ⊎-cong id ⟩
  Any P [] ⊎ Any P xs  □
Any-take-drop P (suc n) {xs} =
  Any P xs                                                 ↔⟨ Any-head-tail P ⟩
  P (head xs) ⊎ Any P (tail xs)                            ↔⟨ id ⊎-cong Any-take-drop P n ⟩
  P (head xs) ⊎
    (Any P (take n (tail xs)) ⊎ Any P (drop n (tail xs)))  ↔⟨ ⊎-assoc ⟩
  (P (head xs) ⊎ Any P (take n (tail xs))) ⊎
    Any P (drop n (tail xs))                               ↔⟨ inverse $ L.Any-∷ P ⊎-cong id ⟩
  Any P (L._∷_ (head xs) (take n (tail xs))) ⊎
    Any P (drop n (tail xs))                               □
