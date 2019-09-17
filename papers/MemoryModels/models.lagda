\AgdaHide{
\begin{code}
module models where
\end{code}
}

%<*memory>
\begin{code}
postulate Label : Set

Memory : Set → Set
Memory V = Label → V
\end{code}
%</memory>
