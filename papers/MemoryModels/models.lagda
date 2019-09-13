\AgdaHide{
\begin{code}
module models where
\end{code}
}

%<*labels>
\begin{code}
open import Relation.Binary using (Setoid)

-- This shouldn't really be ∀ c ℓ, not sure what the best
-- approach is with levels here
postulate Labels : ∀ {c ℓ} → Setoid c ℓ
\end{code}
%</labels>
