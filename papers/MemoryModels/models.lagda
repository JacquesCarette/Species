\AgdaHide{
\begin{code}
module models where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Function using (_∘_; _$_)
\end{code}
}

%<*naivememory>
\begin{code}
Memory0 : ∀ {ℓ v : Level} → Set ℓ → Set v → Set (ℓ ⊔ v)
Memory0 L V = L → V

lookup0 : ∀ {ℓ v} {L : Set ℓ} {V : Set v} → Memory0 L V → L → V
lookup0 m l = m l
\end{code}
%</naivememory>

%<*relabel>
\begin{code}
relabel : {ℓ ℓ′ v : Level} {L : Set ℓ} {L′ : Set ℓ′} {V : Set v} → (L′ → L) → Memory0 L V → Memory0 L′ V
relabel f m = m ∘ f
\end{code}
%</relabel>

But we want to allow wider kinds of models, so we start
defining an interface.
\begin{code}
record Memory {ℓ v s : Level} (L : Set ℓ) (V : Set v) : Set (ℓ ⊔ v ⊔ lsuc s) where
  field
    Mem : Set s
    lookup : Mem → L → V
\end{code}
We shoud check that functions are a model, with application as |lookup|:
\begin{code}
FnAsMemory : {ℓ v s : Level} (L : Set ℓ) (V : Set v) → Memory L V
FnAsMemory L V = record { Mem = L → V ; lookup = _$_ }
\end{code}
