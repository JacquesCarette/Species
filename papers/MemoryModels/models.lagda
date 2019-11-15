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
MemoryF1 = record
  {  Mem      = λ L V → (L → V)
  ;  lookup   = _$_
  ;  relabel  = λ f m → m ∘ f
  }
\end{code}
%</fnasmemory-relabel>

|Memory0| and |Memory1| are very general models of memory,
and work for any types. We would like to narrow things down a little
bit, and look at what might constitute a type.  We still want
to be polymorphic over values, but would rather have the type
of labels be a \emph{parameter}.

\begin{code}
record Memory2 {ℓ v s : Level} (L : Set ℓ) : Set (ℓ ⊔ lsuc v ⊔ lsuc s) where
  field
    Mem : Set v → Set s
    lookup : Mem V → L → V
\end{code}
We drop 'relabel' as it involves a different label set, which
will come in later.

What about the case of a label set with a single label?
\begin{code}
data Single : Set₀ where
  𝟙 : Single
\end{code}

We can then give several very similar-looking implementations:
\begin{code}
MemoryF2-1 : Memory2 {v = v} Single
MemoryF2-1 = record
  { Mem = λ V → (Single → V)
  ; lookup = _$_
  }
MemoryF2-2 : Memory2 {v = v} Single
MemoryF2-2 = record
  { Mem = λ V → (Single → V)
  ; lookup = λ f _ → f 𝟙
  }
MemoryF2-3 : Memory2 {v = v} Single
MemoryF2-3 = record
  { Mem = λ V → (Single → V)
  ; lookup = λ f 𝟙 → f 𝟙
  }
\end{code}

It is easy to think that these are all the same and rather trivial: they
all contain a single value of |V|
\begin{code}
data SingleToo : Set₀ where
  𝟚 : SingleToo
\end{code}

BAY: Just to play devil's advocate, why does the difference matter?
We've already said that we require lookup to be a *total* function.
So what difference does it make if it is strict?  Non-strictness seems
like just an optimization.  Remember we are just using Agda as a
metalogic.  Functions are well-defined mathematical entities; their
specific computational behavior when actually implemented isn't really
important, is it?

%%%%%%%%%%%%%

When talking about labels and memory, it is sometimes easy to get
confused and have the ``wrong'' picture in mind --- such as the
typical C view of linked lists.  So consider the following
types:

[BAY: What is meant by the "typical C view of linked lists"?]
\begin{code}
module _ {V : Set v} where

  record XYZ : Set (lsuc v) where
    field
      x : V
      y : V
      z : V

  record ABC : Set (lsuc v) where
    field
      a : V
      b : V
      c : V

  data Foo : Set (lsuc v) where
    mkFoo : V → V → V → Foo
\end{code}
First and foremost, all $3$ types are obviously equivalent.
Second, and perhaps less obvious, is that the field labels
x,y,z, and a,b,c, are ``virtual'', in the sense that if we
compile a program that uses those records, the labels will
be nowhere to be found in the executable. So the proper
picture of both those types is indeed like Figure ???.
Third is that |Foo| does have labels too, but these are
positional labels in the language syntax; in the internal
representation, these exist as the natural numbers
$0$, $1$ and $2$. They are just even more hidden.

This is stark contrast with
\begin{code}
  data Lbl : Set where
    A B C : Lbl

  Bar : Set v
  Bar = Lbl → V
\end{code}
where the labels now are quite explicitly in the
language itself\footnote{though they will still not
appear in the executable in that form, as they will be
encoded, likely using integers.}.

Lastly, it would be incorrect to assume that, in practice, the
compiler will choose to put the data for each of the above in
the ``obvious layout'', i.e. sequentially in memory, in the same
order as they have been defined.  There is, in fact, no necessary
commitment to do so.  Yes, we are used to low-level languages like
C make layout commitments, which clouds our vision.  But there is no
actual reason the compiler must be so constrained; a sufficiently
smart compiler might notice usage patterns that could be better
handled with a different ordering and, unless the semantics of the
language is explicit about layout, should feel free to choose
an order that seems best.
