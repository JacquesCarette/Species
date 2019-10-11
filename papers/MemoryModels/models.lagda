\AgdaHide{
\begin{code}
module models where

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Function using (_∘_; _$_)
\end{code}
}

%<*naivememory>
\begin{code}
Memory0 : {ℓ v : Level} → Set ℓ → Set v → Set (ℓ ⊔ v)
Memory0 L V = L → V

lookup0 : {ℓ v : Level} {L : Set ℓ} {V : Set v} → Memory0 L V → L → V
lookup0 m l = m l
\end{code}
%</naivememory>

%<*variable>
\begin{code}
variable
  ℓ ℓ′ v  : Level
  L       : Set ℓ   --- an arbitrary set of labels
  L′      : Set ℓ′  --- a different arbitrary set of labels
  V       : Set v   --- a set of values
\end{code}
%</variable>

%<*naivememory2>
\begin{code}
Memory1 : Set ℓ → Set v → Set (ℓ ⊔ v)
Memory1 L V = L → V

lookup1 : Memory1 L V → L → V
lookup1 m l = m l
\end{code}
%</naivememory2>

%<*relabel>
\begin{code}
relabel : (L′ → L) → Memory0 L V → Memory0 L′ V
relabel f m = m ∘ f
\end{code}
%</relabel>

But we want to allow wider kinds of models, so we start
defining an interface.
%<*memrecord>
\begin{code}
record Memory {s : Level} (L : Set ℓ) (V : Set v) : Set (ℓ ⊔ v ⊔ lsuc s) where
  field
    Mem     : Set s
    lookup  : Mem → L → V
\end{code}
%</memrecord>
We shoud check that functions are a model, with application as |lookup|:
%<*fnasmemory>
\begin{code}
FnAsMemory : (L : Set ℓ) → (V : Set v) → Memory L V
FnAsMemory L V = record { Mem = L → V ; lookup = _$_ }
\end{code}
%</fnasmemory>
