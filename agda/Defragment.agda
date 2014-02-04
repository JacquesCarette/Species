open import HoTT

module Defragment where

  data Fin : ℕ -> Set where
    fO : {n : ℕ} -> Fin (S n)
    fS : {n : ℕ} -> Fin n -> Fin (S n)

  record _⊆_ (A : Set) (B : Set) : Set where
    field
      embed : A -> B
      project : B -> Coprod Unit A
      rtL : (a : A) -> project (embed a) == inr a
      rtR : (b : B) (a : A) -> project b == inr a -> embed a == b

  Finite : Set -> Set
  Finite L = Σ ℕ (λ n → L ≃ Fin n)

  distributeR : {A : Set} {P Q : A -> Set}
             → Σ A (λ a → Coprod (P a) (Q a)) -> Coprod (Σ A P) (Σ A Q)
  distributeR (a , inl p) = inl (a , p)
  distributeR (a , inr q) = inr (a , q)

  distributeL : {A : Set} {P Q : A -> Set}
             → Coprod (Σ A P) (Σ A Q) -> Σ A (λ a → Coprod (P a) (Q a))
  distributeL (inl (a , p)) = a , inl p
  distributeL (inr (a , q)) = a , inr q

  distributeRL : {A : Set} {P Q : A -> Set} ->
    (b : Coprod (Σ A P) (Σ A Q)) -> distributeR (distributeL b) == b
  distributeRL (inl (_ , _)) = idp
  distributeRL (inr (_ , _)) = idp

  distributeLR : {A : Set} {P Q : A -> Set} ->
    (b : Σ A (λ a → Coprod (P a) (Q a))) -> distributeL (distributeR b) == b
  distributeLR (_ , inl _) = idp
  distributeLR (_ , inr _) = idp

  distribute : {A : Set} {P Q : A -> Set}
             → Σ A (λ a → Coprod (P a) (Q a)) ≃ Coprod (Σ A P) (Σ A Q)
  distribute = equiv distributeR distributeL distributeRL distributeLR

  module Defragment
           (L : Set)
           (n : ℕ)
           (sub : L ⊆ Fin n)
           (gcbp : {A B A' B' : Set} -> (Coprod A A' ≃ Coprod B B') -> (A' ≃ B') -> (A ≃ B)) where

    open _⊆_

    D1' : Set
    D1' = Σ (Fin n) (λ k → Coprod (Σ L (λ l → project sub k == inr l))
                                  (project sub k == inl unit))

    D1 : Set
    D1 = Coprod (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l)))
                (Σ (Fin n) (λ k → project sub k == inl unit))

    g1' : Fin n -> D1'
    g1' k = k , match_withl_withr_ {C = λ prj → Coprod (Σ L (λ l → prj == inr l))
                                                       (prj == inl unit) }
             (project sub k)
             (λ unit → inr idp)
             (λ l → inl (l , idp))

    -- g1'fst ( k , pq ) = {!!}

    decomp1' : D1' ≃ Fin n
    decomp1' = equiv fst g1' (λ _ → idp) (λ a → pair= idp {!!})
      -- where
      --   foo : (a : D1') → match project sub (fst a) withl (λ unit₁ → inr idp) withr (λ l → inl (l , idp)) == snd a
      --   foo = {!!}

    decomp1 : D1 ≃ Fin n
    decomp1 = D1 ≃⟨ distribute ⁻¹ ⟩ D1' ≃⟨ decomp1' ⟩ Fin n ≃∎

    Fin- : ℕ -> ℕ -> Set
    Fin- n s = Σ ℕ (λ j → Σ (j + s == n) (λ _ → Fin j))

    D2 : (s : ℕ) → Set
    D2 s = Coprod (Fin s) (Fin- n s)

    decomp2 : (s : ℕ) → Fin n ≃ D2 s
    decomp2 O = {!!}
    decomp2 (S s) = {!!}

    Lsize : Σ ℕ (λ sz → (Σ (Fin n) (λ k → project sub k == inl unit)) ≃ Fin- n sz)
    Lsize = {!!}

    ∣L∣ : ℕ
    ∣L∣ = fst Lsize

    quux : (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l))) ≃ Fin ∣L∣
    quux = gcbp (decomp2 ∣L∣ ∘e decomp1) (snd Lsize)

    baz1 : L → (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l)))
    baz1 l = embed sub l , (l , rtL sub l)

    baz2 : (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l))) → L
    baz2 (_ , (l , _)) = l

    baz : L ≃ (Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l)))
    baz = equiv baz1 baz2 bazpf1 (λ _ → idp)
      where
        bazpf1 : (b : Σ (Fin n) (λ k → Σ L (λ l → project sub k == inr l))) →
           (embed sub (fst (snd b)) , (fst (snd b) , rtL sub (fst (snd b)))) == b
        bazpf1 (k , (l , e)) = {!!}

          -- J {A = Coprod Unit L} (λ _ p → (embed sub l , (l , rtL sub l)) == (k , (l , p))) {!!} {a' = (k , (l , e))} e

          -- (embed sub l , (l , rtL sub l)) == (k , (l , e))

          -- pair=
          --   (rtR sub k l e) {!!}

            -- (J' (λ _ p → PathOver (λ v → Σ L (λ l₁ → project sub v == inr l₁))
            --                       (rtR sub k l p) (l , rtL sub l) (l , p))
            --     ? ?)

    frob : L ≃ Fin ∣L∣
    frob = quux ∘e baz

    defragment : Finite L
    defragment = ∣L∣ , frob
