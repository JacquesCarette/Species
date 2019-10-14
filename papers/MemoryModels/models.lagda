\AgdaHide{
\begin{code}
module models where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Function using (_∘_; _$_)
\end{code}
}

%<*naivememory>
\begin{code}
MemoryF : {ℓ v : Level} → Set ℓ → Set v → Set (ℓ ⊔ v)
MemoryF L V = L → V

lookupF : {ℓ v : Level} {L : Set ℓ} {V : Set v} → MemoryF L V → L → V
lookupF m l = m l
\end{code}
%</naivememory>

%<*variable>
\begin{code}
variable
  ℓ ℓ′ v s : Level
  L        : Set ℓ   --- an arbitrary set of labels
  L′       : Set ℓ′  --- a different arbitrary set of labels
  V        : Set v   --- a set of values
\end{code}
%</variable>

%<*naivememory2>
\begin{code}
MemoryF′ : Set ℓ → Set v → Set (ℓ ⊔ v)
MemoryF′ L V = L → V

lookupF′ : MemoryF′ L V → L → V
lookupF′ m l = m l
\end{code}
%</naivememory2>

%<*relabel>
\begin{code}
-- relabel : (L′ → L) → MemoryF L V → MemoryF L′ V
-- relabel f m = m ∘ f
\end{code}
%</relabel>

But we want to allow wider kinds of models, so we start
defining an interface.
%<*memrecord>
\begin{code}
record Memory0 : Set (lsuc ℓ ⊔ lsuc v ⊔ lsuc s) where
  field
    Mem     : (L : Set ℓ) → (V : Set v) → Set s
    lookup  : Mem L V → L → V
\end{code}
%</memrecord>
We shoud check that functions are a model, with application as |lookup|:
%<*fnasmemory>
\begin{code}
MemoryF0 : {ℓ v : Level} → Memory0 {ℓ} {v}
MemoryF0 = record { Mem = λ L V → (L → V) ; lookup = _$_ }
\end{code}
%</fnasmemory>

The next iteration of the interface, with relabelling:
%<*memrecord-relabel>
\begin{code}
record Memory1 : Set (lsuc ℓ ⊔ lsuc v ⊔ lsuc s) where
  field
    Mem     : (L : Set ℓ) → (V : Set v) → Set s
    lookup  : Mem L V → L → V
    relabel : (L′ → L) → Mem L V → Mem L′ V
\end{code}
%</memrecord-relabel>

%<*fnasmemory-relabel>
\begin{code}
MemoryF1 : {ℓ v : Level} → Memory1 {ℓ} {v}
MemoryF1 = record { Mem = λ L V → (L → V) ; lookup = _$_ ; relabel = λ f m → m ∘ f }
\end{code}
%</fnasmemory-relabel>
