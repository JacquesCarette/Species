open import Function.Inverse

module InverseLemmas where

∘r-inverse : ∀ {A B C : Set} → (A ↔ B) → (B ↔ C) ↔ (A ↔ C)
∘r-inverse a↔b = record { to = record { _⟨$⟩_ = λ b↔c → (b↔c ∘ a↔b); cong = λ x → {!!} }; from = {!!}; inverse-of = {!!} }
