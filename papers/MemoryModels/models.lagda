\AgdaHide{
\begin{code}
module models where

open import Function using (_∘_)
\end{code}
}

%<*memory>
\begin{code}
postulate Label : Set

Memory : Set → Set → Set
Memory L V = L → V
\end{code}
%</memory>

%<*relabel>
\begin{code}
relabel : ∀ {L L' V} → (L' → L) → Memory L V → Memory L' V
relabel f m = m ∘ f
\end{code}
%</relabel>
