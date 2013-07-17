%% -*- LaTeX -*-

\documentclass[9pt,preprint,authoryear]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%format sumTys = "\cons{sumTys}"
%format <->    = "\iso"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{../species}

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{proof}
\usepackage{comment}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Page size

\pdfpagewidth=8.5in
\pdfpageheight=11in

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Theorems etc.

\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}

\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{graphicx}
\usepackage[outputdir=diagrams/,backend=ps,extension=eps]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

% Use sans-serif for math operators
\DeclareSymbolFont{sfoperators}{OT1}{cmss}{m}{n}
\DeclareSymbolFontAlphabet{\mathsf}{sfoperators}

\makeatletter
\def\operator@@font{\mathgroup\symsfoperators}
\makeatother

\newcommand{\lam}[2]{\lambda #1 . #2}

\newcommand{\iso}{\leftrightarrow}
\newcommand{\mkIso}{\rightleftharpoons}

\newcommand{\impl}[1]{\ensuremath{\{#1\}}} % implicit arguments
\newcommand{\defn}{\vcentcolon\equiv}

\newcommand{\TyZero}{\ensuremath{\bot}}
\newcommand{\TyOne}{\ensuremath{\top}}
\newcommand{\unit}{\ensuremath{\langle\rangle}}

\newcommand{\cons}[1]{\ensuremath{\mathsf{#1}}}

\DeclareMathOperator{\Species}{Species}
\DeclareMathOperator{\FinType}{FinType}
\DeclareMathOperator{\Type}{Type}
\DeclareMathOperator{\Fin}{Fin}
\DeclareMathOperator{\IsFinite}{IsFinite}
\DeclareMathOperator{\NatZ}{O}
\DeclareMathOperator{\NatS}{S}
\DeclareMathOperator{\FinZ}{fO}
\DeclareMathOperator{\FinS}{fS}
\DeclareMathOperator{\Vect}{Vec}
\DeclareMathOperator{\id}{id}
\DeclareMathOperator{\shapes}{shapes}
\DeclareMathOperator{\relabel}{relabel}
\DeclareMathOperator{\Natural}{Natural}
\DeclareMathOperator{\OfSize}{OfSize}

\DeclareMathOperator{\map}{map}
\DeclareMathOperator{\sumTys}{sumTys}

\DeclareMathOperator{\Elim}{Elim}
\DeclareMathOperator{\elim}{elim}
\DeclareMathOperator{\DecEq}{DecEq}

\newcommand{\mor}{\Rightarrow}
% \newcommand{\mor}{\stackrel{\bullet}{\rightarrow}}
\newcommand{\natiso}{\Leftrightarrow}
% \newcommand{\natiso}{\stackrel{\bullet}{\longleftrightarrow}}

\newcommand{\ssum}{\boxplus}
\newcommand{\sprod}{\boxdot}
\newcommand{\scomp}{\boxcircle}
\newcommand{\scprod}{\boxtimes}
\newcommand{\fcomp}{\boxbox}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\sect\ref{#1}}
\newrefformat{eq}{equation~\eqref{#1}}
\newrefformat{prob}{Problem~\ref{#1}}
\newrefformat{tab}{Table~\ref{#1}}
\newrefformat{thm}{Theorem~\ref{#1}}
\newrefformat{lem}{Lemma~\ref{#1}}
\newrefformat{prop}{Proposition~\ref{#1}}
\newrefformat{defn}{Definition~\ref{#1}}
\newrefformat{cor}{Corollary~\ref{#1}}
\newcommand{\pref}[1]{\prettyref{#1}}

% \Pref is just like \pref but it uppercases the first letter; for use
% at the beginning of a sentence.
\newcommand{\Pref}[1]{%
  \expandafter\ifx\csname r@@#1\endcsname\relax {\scriptsize[ref]}
    \else
    \edef\reftext{\prettyref{#1}}\expandafter\MakeUppercase\reftext
    \fi
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Comments

% big, top-level (verbatim) comments

\specialcomment{todoP}{\begingroup\color{red}TODO: }{\endgroup}

% quick (inline) comments

\newif\ifcomments\commentstrue

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}
\newcommand{\etal}{\emph{et al.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\title{Species Constructors}

\authorinfo{Brent A. Yorgey \\ Stephanie Weirich}
{Dept. of Computer and Information Science\\ The University of Pennsylvania\\
Philadelphia, Pennsylvania, USA}
{\{byorgey,sweirich\}@@cis.upenn.edu}

\authorinfo{Jacques Carette}
{Dept. of Computing and Software\\ McMaster University\\
Hamilton, Ontario, Canada}
{carette@@mcmaster.ca}

\maketitle

\begin{abstract}

\todo{Abstract goes here.}

\end{abstract}

\category{D.3.2}{Programming Languages}{Applicative (functional) languages}

\terms
Languages, Types

\section{Introduction}
\label{sec:intro}

\begin{todoP}
  Motivation.  ``An answer looking for a question.''  Note symmetries
  were original motivation, but drawn to labels instead.  ``Follow the
  theory'' and see what pops out.

  Take-home points:
  \begin{itemize}
  \item Labelled structures capture a wide range of data structures.
  \item Combinators! ($\times 2!$ --- type level and value level)
  \end{itemize}

  Other interesting but not take-home points:
  \begin{itemize}
  \item fun with isos
  \item labels as abstract model of memory
  \item labels make sharing easy
  \end{itemize}
\end{todoP}

The idea of separating shapes and data is not new \todo{citations:
  containers, shapely types, etc.}.  However, previous approaches have
left the labels \emph{implicit}.  Bringing the labels to the fore
enables cool stuff like
\begin{itemize}
\item include a bunch of disparate stuff
  under one framework
\item let us talk about relabelling as a separate
  operation
\item put structure on the labels themselves, e.g. L-species
\item \todo{more?}
\end{itemize}

\section{Labelled Structures}
\label{sec:labelled}

Rather than diving immediately into species, we begin with an
intuitive definition of ``labelled structures'' and some examples.

The essential idea of labelled structures is to separate the notions
of container shapes and the data stored in those shapes.  This idea in
and of itself is not new \cite{shapely, containers}; what is new is
putting \emph{labels} front and center.  Labels provide the missing
link between shapes and data, allowing one to specify which data goes
where. \todo{say a bit more? Labels do more than that, which is why
  bringing them to the fore is interesting.}

Informally, a \term{labelled structure} is specified by:
\begin{itemize}
\item a finite type of labels $L$;
\item a type of data elements $A$;
\item some sort of ``labelled shape''; and
\item a (total) function $v : L \to A$ which maps labels to data values.
\end{itemize}
See~\pref{fig:labelled-structure-example} for an abstract example.  A
\emph{family} of labelled structures refers to a class of structures
parameterized over the label type $L$ and data type $A$.

\begin{figure}
  \centering
\begin{diagram}[width=200]
import Graphics.SVGFonts.ReadFont
import Diagrams.Points
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import SpeciesDiagrams

mkL n = text' (show n) <> circle 0.7 # fc white

t = Node 2 [Node 1 [], Node 4 [Node 3 [], Node 0 [], Node 5 []]]

d = renderTree mkL (~~) (symmLayout' with { slHSep = 3.5, slVSep = 3.5 } t)

mapping = centerY . vcat' with {sep = 0.3} $ zipWith mkMapping [0..5] "SNAILS" -- $
  where
    mkMapping i c = mkL i .... hrule 1 .... (text' (show c) <> strutX 1)

dia = (d # centerY ... strutX 4 ... mapping)
    # centerXY # pad 1.1

infixl 6 ...
infixl 6 ....
(...) = (||||||)
x .... y = x ... strutX 0.5 ... y
\end{diagram}
  \caption{A labelled structure with six labels}
  \label{fig:labelled-structure-example}
\end{figure}

Note that the function $v : L \to A$ mapping labels to data values
need not be injective, so the same value of type $A$ may be associated
to multiple labels, as illustrated in
\pref{fig:labelled-structure-example}.  However, each label must
``occur exactly once'' in the sense that $v$ must be total and cannot
associate the same label to multiple values.  Abstractly, the labels
can be thought of as ``holes'' or ``positions'' in the labelled shape
which are to be filled with data.

For now, we leave the notion of ``labelled shape'' abstract; we will
return to define it more precisely in \pref{sec:species}.

\paragraph{Algebraic data types}

All the usual algebraic data types can be viewed as families of
labelled structures.  For example, \todo{example}.  Note, however, that
the family of labelled tree structures is quite a bit larger than the
usual algebraic type of trees: every possible different way of
labelling a given tree shape results in a different labelled
structure.  For algebraic data types, this added structure is
uninteresting, in a way that we will make precise later
\todo{when?}. \bay{Idea here is that for regular species we can always
  recover a canonical labelling from the shape; and moreover there are
  always precisely $n!$ different labellings for a shape of size $n$
  (given a fixed set of labels).}

\paragraph{Finite maps}

Since the definition of a labelled structure already includes the
notion of a mapping from labels to data, we may encode finite maps
simply by using \emph{sets} of labels as shapes, \ie\ shapes with no
structure other than containing some labels.

\todo{picture?}

\paragraph{Vectors and arrays}

Vectors, and multi-dimensional arrays more generally, \todo{from one
  point of view are just finite maps with some nontrivial structure on
  the labels.  Can also move the structure around between labels and
  shape (???).}

\paragraph{Symmetric shapes}

We have not yet defined precisely what counts as a ``shape'', but one
interesting possibility is the use of shapes with some sort of
\term{symmetry}.  For example, a \term{cycle} is like a list, except
that it is invariant under cyclic rotation of its labels.  One area
where cycles are especially useful is in computational geometry: we
can represent an (oriented) polygon, for example, as a labelled cycle
shape, with each label mapping to a point in space.

\todo{picture of a polygon represented with labelled cycle}

\bay{should we include cycles at all?  Our system can't handle them
  although they fit from a theoretical point of view\dots}

An \emph{unordered pair} is another sort of shape with symmetry: it is
like an ordered pair but invariant under swapping.  Unordered pairs
can be used to represent undirected graph edges, \todo{other stuff?}

\paragraph{Value-level sharing}

\bay{
e.g. $\L \times \F$
}

\paragraph{Graphs}

\bay{
can we do graphs?
}

% \todo{
%   Pedagogical, fun examples. (Map, vector, tree, edges/triangulations)
%   Enough background just-in-time.
% }

\section{Combinatorial Species}
\label{sec:species}

\bay{The other thing to point out somewhere is that tracking labels is to
  tracking size as the category B is to the discrete category of
  natural numbers---i.e. it is a ``categorification''.}

% We want to think of each labeled structure as \emph{indexed by} its
% set of labels (or, more generally, by the \emph{size} of the set of
% labels).  We can accomplish this by a mapping from label sets to all
% the structures built from them, with some extra properties to
% guarantee that we really do get the same family of structures no
% matter what set of labels we happen to choose.

Our theory of labelled structures is inspired by, and directly based
on, the theory of \term{combinatorial species} \cite{joyal, bll}.
\todo{point the reader to our own prior work on species + FP}

\todo{Note that a lot of the power of the theory for combinatorics
  comes from homomorphisms to rings of formal power series; we won't
  use that in this paper---future work.}

\subsection{Species, set-theoretically}
\label{sec:set-species}

We begin with a standard set-theoretic definition of species
(essentially what one finds in Bergeron \etal \cite{bll}, but with
slightly different terminology).  We will upgrade to a
\emph{type}-theoretic definition in \pref{sec:constructive-species},
but include this version for completeness and to help build intuition.

\begin{definition}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $L$ (of \term{labels}) to a finite set
  $F(L)$ (of \term{shapes}), and
\item sends any bijection on finite sets $\sigma : L \iso L'$ (a
  \term{relabelling}) to a function $F(\sigma) : F(L) \to F(L')$
  (illustrated in \pref{fig:relabelling}),
\end{itemize}
additionally satisfying the following functoriality conditions:
\begin{itemize}
\item $F(id_L) = id_{F(L)}$, and
\item $F(\sigma \circ \tau) = F(\sigma) \circ F(\tau)$.
\end{itemize}
\end{definition}

% \begin{figure}
%   \centering
%   \includegraphics{relabelling}
%   \caption{Relabelling}
%   \label{fig:relabelling}
% \end{figure}
% \later{redraw this with diagrams}

Using the language of category theory, this definition can be pithily
summed up by saying that a species is a functor $F : \B \to
\FinSet$, where $\B$ is the category of finite sets whose morphisms
are bijections, and $\FinSet$ is the category of finite sets whose
morphisms are arbitrary (total) functions.

We call $F(L)$ the set of ``$F$-shapes with
labels drawn from $L$'', or simply ``$F$-shapes on $L$'', or even
(when $L$ is clear from context) just ``$F$-shapes.  $F(\sigma)$
is called the ``transport of $\sigma$ along $F$'', or sometimes the
``relabelling of $F$-shapes by $\sigma$''.

Note that in the existing literature, elements of $F(L)$ are usually
called ``$F$-structures'' rather than ``$F$-shapes''.  To a
combinatorialist, labelled shapes are themselves the primary objects
of interest; however, in a computational context, we must be careful
to distinguish between labelled \emph{structures} (which have data
associated with the labels) and bare labelled \emph{shapes} (which do
not).

Here we see that the formal notion of ``shape'' is actually quite
broad, so broad as to make one squirm: a shape is just an element of
some arbitrary finite set!  In practice, however, we are interested
not in arbitrary species but in ones built up algebraically from a set
of primitives and operations.  In that case the corresponding shapes
will have more structure as well. First, however, we must put species
and labelled structures on a firmer computational basis.

\subsection{Species, constructively}
\label{sec:constructive-species}

The foregoing set-theoretic definition of species is perfectly
serviceable in the context of classical combinatorics, but in order to
use it as a foundation for data structures, it is necessary to first
``port'' the definition from set theory to constructive type theory.

\todo{this section is too dense}
In the remainder of this paper, we work within a standard variant of
Martin-L\"of dependent type theory \cite{martin-lof} (precisely
\emph{which} variant we use probably does not matter very much),
equipped with an empty type \TyZero, unit type \TyOne, coproducts,
dependent pairs, dependent functions, a universe $\Type$ of types, and
a notion of propositional equality. For convenience, instead of
writing the traditional $\sum_{x : A} B(x)$ and $\prod_{x:A} B(x)$ for
dependent pair and function types, we will use the Agda-like
\cite{Agda} notations $(x:A) \times B(x)$ and $(x:A) \to B(x)$,
respectively.  We continue to use the standard abbreviations $A \times
B$ and $A \to B$ for non-dependent pair and function types, that is,
when $x$ does not appear free in $B$.  We write $\impl{x:A} \to B$ for
the type of functions taking $x$ as an \emph{implicit} argument, and
omit implicit arguments when applying such functions.  For example, if
$f : \impl{A:\Type} \to A \to A$ then we write simply $f\ 3$ instead of
$f\ \N\ 3$.  When an implicit argument needs to be provided explicitly
we use a subscript, as in $f_{\N}\ 3$.

We use $\N : \Type$ to denote the usual inductively defined type of
natural numbers, with constructors $\NatZ : \N$ and $\NatS : \N \to
\N$.  We also make use of the usual indexed type of canonical finite
sets $\Fin : \N \to \Type$, with constructors $\FinZ : \impl{n :
\N} \to \Fin (\NatS n)$ and $\FinS : \impl {n : \N} \to \Fin n \to \Fin
(\NatS n)$.

$A \iso B$ is the type of isomorphisms between $A$ and $B$, \ie\ pairs
of inverse functions $f : A \to B$ and $g : B \to A$.  We overload the
notations $\id$ and $\comp$ to denote the identity isomorphism and
isomorphism composition respectively; we also allow isomorphisms of
type $A \iso B$ to be implicitly used as functions $A \to B$ where it
does not cause confusion.  We use the notation $\mkIso$ for
constructing isomorphisms from a pair of functions. That is, if $f : A
\to B$ and $g : B \to A$ are inverse, then $f \mkIso g : A \iso B$;
the proof that $f$ and $g$ are inverse is left implicit.  For
admissible $T : \Type \to \Type$ and $\sigma : A \iso B$ we can also
construct the isomorphism $T\ \sigma : T\ A \iso T\ B$. For example,
$\sigma \times (\sigma \to C) : A \times (A \to C) \iso B \times (B
\to C)$, given by \[ \sigma \times (\sigma \to C) =
(\lam{(a,f)}{(\sigma\ a, f \comp \sigma^{-1})} \mkIso (\lam{(b,g)}{(\sigma^{-1}\ b, f \comp \sigma)}) \]

With the preliminaries out of the way, The first concept we need to
port is that of a finite set.  Constructively, a finite set is one
with an isomorphism to $\Fin\ n$ for some natural number $n$. That is,
\[ \IsFinite A \defn (n : \N) \times (\Fin n \iso A). \] \bay{Note
  there are other notions of finiteness but this is the one we
  want/need?  See \eg\ \url{http://ncatlab.org/nlab/show/finite+set}.}
Then we can define \[ \FinType \defn (A : \Type) \times \IsFinite A \] as
the universe of finite types.

\todo{need some nice notation for dependent $n$-tuples, \ie\ records.}

\bay{in the set-theory section we said the codomain of species is
  \emph{finite} types, but in this definition the codomain is $\Type$
  rather than $\FinType$.  What's going on? Certainly the finiteness
  of the codomain does not seem to be that important---it doesn't come
  up at all in our implementation, which is why I didn't notice the
  discrepancy at first. I suppose it only becomes important when one
  wants to do things like map to generating functions.  Following a
  discussion with Stephanie, it seems that quite a few theorems about
  species (molecular decomposition, maybe implicit species theorem)
  may actually depend on the finiteness, but it's hard to be sure.
  Would be interesting to try to port the theorems and proofs as well
  as the definition.}

\begin{align*}
\Species & \defn (\shapes : \FinType \to \Type) \\
         & \times (\relabel : (\FinType \iso \FinType) \to
           (\Type \to \Type)) \\
         & \times ((L : \FinType) \to \relabel \id_L = \id_{(\shapes L)}) \\
         & \times ((L_1, L_2, L_3 : \FinType) \to (\sigma : L_2 \iso
         L_3) \\ &\to (\tau : L_1 \iso L_2) \to
(\relabel (\sigma \comp \tau) = \relabel \sigma \comp \relabel \tau))
\end{align*}

Where the meaning is clear from context, we will use simple
application to denote the action of a species on both objects and
arrows. That is, if $F : \Species$, instead of writing $F.\shapes\ L$
or $F.\relabel\ \sigma$ we will just write $F\ L$ or $F\
\sigma$.

\subsection{Labelled structures, formally}
\label{sec:labelled-formal}

Formally, we may define a labelled structure as a dependent five-tuple
with the type
\[
   (F : \Species) \times (L : \FinType) \times (A : \Type) \times F\ L
   \times (L \to A),
\]
that is,
\begin{itemize}
\item a species $F$,
\item a constructively finite type $L$ of \term{labels},
\item a type $A$ of \term{data},
\item a shape of type $F\ L$, \ie\ an $L$-labelled $F$-shape,
\item a mapping from labels to data, $m : L \to A$.
\end{itemize}

We can define the generic type of eliminators for labelled
$F$-structures, $\Elim_F : \Type \to \Type \to \Type$, as
\begin{multline*}
  \Elim_F\ A\ R \defn (L : \Type) \to \\
  \DecEq L \to F\ L \to (L \to A) \to R
\end{multline*}
where $\DecEq L$ represents decidable equality for $L$. There are a
few subtle issues here which are worth spelling out in detail. First,
note that $\Elim_F$ is parameterized by $A$ (the type of data elements
stored in the labelled structure being eliminated) and $R$ (the type
of the desired result), but \emph{not} by $L$.  Rather, an eliminator
of type $\Elim_F\ A\ R$ must be parametric in $L$; it is not allowed
to define an eliminator which works only for certain label types.  The
second point is that $L$ is a $\Type$ rather than a $\FinType$ as one
might expect.  The reason is that one can observe an induced linear
order on the elements of a $\FinType$, using the usual linear order on
the associated natural numbers, but we do not want to allow this,
since it would ``break'' the functoriality of species.  \bay{is this
  the right way to say it?}  That is, an eliminator which was allowed
to observe an implicit linear order on the labels could give different
results for two labelled structures which differ only by a
relabelling, \bay{but this is bad... why?} Instead, we require only
decidable equality for $L$ (of course, every $\FinType$ has decidable
equality).

We can ``run'' an eliminator,
\[ \elim : \Elim_F\ A\ R \to ??? \to R, \] by simply taking apart the
labelled structure and passing its components to the eliminator,
projecting the label $\Type$ and its decidable equality from the
$\FinType$.

\todo{Note all the stuff with $L$ really only makes a difference for
  things with sharing\dots}

\subsection{Species, algebraically}
\label{sec:algebraic}

We now return to the observation from \pref{sec:set-species} that we
do not really want to work directly with the definition of species,
but rather with an algebraic theory. \todo{say a bit more}

For each species primitive or operation, we also discuss the
associated introduction form(s).  We discuss eliminators
in~\pref{sec:elim}.

\paragraph{Zero}
  The \emph{zero} or \emph{empty} species, denoted $\Zero$, is the
  unique species with no shapes whatsoever, defined by its action on
  finite types and bijections as
  \begin{align*}
  \Zero\ L &= \TyZero \\
  \Zero\ \sigma &= \id_\TyZero
  \end{align*}
  The zero species, of course, has no introduction form.
  \bay{Say more here?}

  \todo{be more explicit about how we will be defining species
    implicitly by defining the $\cons{shapes}$ field; $\cons{relabel}$
    can be obtained by the syntactic substitution trick outlined
    below; the proofs are straightforward and omitted.}

\paragraph{One}
  The \emph{one} or \emph{unit} species, denoted $\One$, is the
  species with a single shape of size $0$.  The usual set-theoretic
  definition is
  \[ \One\ L =
  \begin{cases}
    \{\star\} & ||L|| = 0 \\
    \varnothing & \text{otherwise}
  \end{cases}
  \]
  However, this is confusing to the typical type theorist.  First, it
  seems strange that the definition of $\One$ gets to ``look at'' $L$,
  since species are supposed to be functorial.  In fact, the
  definition does not violate functoriality (because it only ``looks
  at'' the size of $L$, not its contents, and bijections preserve
  size), but this is not manifestly obvious. It's also strange that we
  have to pull some arbitrary one-element set out of thin air.

  The corresponding type-theoretic definition, on the other hand, is
  \[ \One\ L = \TyZero \iso L. \] That is, a $\One$-shape consists
  solely of a proof that $\L$ is empty. (By function extensionality,
  for any given type $\L$ there is only one such proof.)  In this
  form, the functoriality of $\One$ is also evident: \[ \One\ \sigma =
  \TyZero \iso \sigma, \] or more explicitly, \[ \One\ \sigma = (\lam
  {\tau}{\sigma \comp \tau}) \mkIso (\lam {\tau}{\sigma^{-1} \comp
    \tau}). \] \bay{Note that something equivalent is mentioned in
    Yeh, “The calculus of virtual species and K-species”, namely that
    $\One$ can be defined as the hom-functor $\B(\varnothing, -)$.}

  There is a trivial introduction form for $\One$, also denoted
  $\top$, which creates a $\One$-shape using the canonical label set
  $\Fin\ 0$, that is, $\top : \One\ (\Fin\ 0)$.  Introducing a
  canonical label type will be standard for introduction forms; other
  label types may be obtained via relabelling.

\paragraph{Singleton}
  The \emph{singleton} species, denoted $\X$, is defined by
  \[ \X\ L = \TyOne \iso L, \] that is, an $\X$-shape is just a proof
  that $L$ has size $1$.  Again, there is at most one such proof.
  Unlike $\One$, we may also think of an $\X$-shape as ``containing''
  a single label of type $L$, which we may recover by applying the
  isomorphism to $\unit$.

  Note that once again the definition is ``obviously'' functorial; we
  may syntactically replace $L$ by $\sigma$ to obtain \[ \X\ \sigma =
  \top \iso \sigma. \]  This will remain true for most \bay{all?} of the
  definitions given from here on. \bay{But we will explicitly discuss
    it when it is not obvious?}

  $\X$-shapes, as with $\One$, have a trivial introduction form,
  \[ \cons{x} : \X\ (\Fin\ 1). \]

\paragraph{Sets}
The species of \emph{sets}, denoted $\E$, is defined by \[ \E\ L =
\TyOne. \] That is, there is a single $\E$-shape for every label type.

\todo{say more here?}

% \footnote{The species literature calls
%     this the species of \emph{sets}, but that's misleading to computer
%     scientists, who expect the word ``set'' to imply that elements
%     cannot be repeated. The \emph{labels} in a bag structure cannot be
%   repeated, but nothing stops us from mapping labels to data elements
%   in a non-injective way.}, denoted $\Bag$, is defined by \[ \Bag[U] =
%   \{U\}, \] that is, there is a single $\Bag$-structure on any set of
%   labels $U$, which we usually identify with the set of labels itself
%   (although we could equivalently define $\Bag[U] = \{\star\}$). The
%   idea is that an $\Bag$-structure consists solely of a collection of
%   labels, with no imposed ordering whatsoever.

%   $\E$ is precisely the species mentioned previously which some
%   na\"ively expect as the definition of $\One$.  In fact, $\E$ is
%   indeed the identity element for a product-like operation,
%   \term{Cartesian product}, to be discussed below.

As a summary, \pref{fig:prims} contains a graphic showing $\Zero$-,
$\One$-, $\X$-, and $\E$-shapes arranged by size (\ie, the size of the
underlying type of labels $L$): a dot indicates a single shape, and
the size of the label type increases from left to right.

\begin{figure}
  \centering
\begin{diagram}[width='200']
import SpeciesDiagrams

dot = circle 0.2 # fc black
row p     = hcat' with {sep=0.1} . map (drawOne . p) $ [0..10]
lRow x p  = (text' [x] <> phantom (square 1 :: D R2)) |||||| strutX 0.5 |||||| row p
drawOne b = square 1 <> mconcat [dot||b]

dia =
  pad 1.1 .
  centerXY .
  vcat' with {sep = 0.3} $
  [ lRow '0' (const False)
  , lRow '1' (==0)
  , lRow 'X' (==1)
  , lRow 'E' (const True)
  ]
\end{diagram}
%$
  \caption{Primitive species}
  \label{fig:prims}
\end{figure}

\subsection{Species isomorphism}
\label{sec:species-iso}

We have now seen four primitive species: \Zero, \One, \X, and \E.  It
turns out that each of them is the unit for a different monoid
structure on species; we will look at each of these in turn, as well
as an additional fifth monoid structure.  Before we get there,
however, we need to take a brief detour to discuss isomorphism of
species, since the monoid laws hold only up to isomorphism.

Since species are functors, a \term{morphism} between species $F$ and
$G$ is a natural transformation, that is, a transformation from
$F$-shapes to $G$-shapes which works uniformly for all label
types. Formally, the type of species morphisms is given by
\begin{align*}
  &- \mor - : \Species \to \Species \to \Type \\
  &F \mor G = (\varphi : \impl{L : \FinType} \to F\ L \to G\ L)
  \times \Natural\ \varphi
\end{align*}
where $\Natural\ \varphi$ is the proposition which states that $\varphi$ is
\term{natural}, that is, the diagram shown in
\pref{fig:species-morphism} commutes for all $L, L' : \FinType$ and
all $\sigma : L \iso L'$.

\begin{figure}[h!]
  \centering
  \centerline{
    \xymatrix{
      F\ L \ar[d]_{\varphi_L} \ar[r]^{F\ \sigma} & F\ L' \ar[d]^{\varphi_{L'}} \\
      G\ L                    \ar[r]_{G\ \sigma} & G\ L'
    }
  }
  \caption{Naturality for species morphisms}
  \label{fig:species-morphism}
\end{figure}

Intuitively, $\varphi$ is natural if it does not depend on the type of
the labels, that is, it acts uniformly for all choices of label set:
it does not matter whether one first relabels an $F$-shape and then
applies $\varphi$, or applies $\varphi$ first and later relabels.

An \term{isomorphism} between species, denoted $F \natiso G$, is just
a pair of inverse morphisms, that is, $\varphi : F \mor G$ and
$\varphi^{-1} : G \mor F$ such that $\varphi^{-1}_L \comp \varphi_L =
id_{FL}$ and $\varphi_L \comp \varphi^{-1}_L = id_{GL}$ for all $L :
\FinType$.  Species isomorphism preserves all the interesting
\emph{combinatorial} properties of species; hence in the combinatorics
literature everything is always implicitly done up to
isomorphism. However, species isomorphisms carry computational
content, so when dealing with labelled structures we must be more
careful and explicit in their use.

It is worth noting that a pair of ``bare'' inverse morphisms, without
naturality, constitute what is termed an \term{equipotence} between
two species.  An equipotence preserves the \emph{number} of shapes of
each size, but it does not necessarily preserve the structure of those
shapes. As a classic example, the species of \emph{lists} and the
species of \emph{permutations} are equipotent but not isomorphic:
there are the same number of lists as permutations of $n$ labels
(namely, $n!$), but there is no way to set up an isomorphism between
them which is uniform over the labels: any such isomorphism
necessarily depends on a linear ordering of the labels.  In a sense,
permutations have ``more structure'' than lists, and this extra
structure cannot be preserved by an isomorphism.  In any case,
although equipotences are of interest to combinatorialists, so far
they do not seem to be of much use computationally, so we will not
consider them further in this paper.

\subsection{Species operations}
\label{sec:species-ops}

\paragraph{Sum}
Given two species $F$ and $G$, we may form their sum. We use $\ssum$
to denote the sum of two species to distinguish it from $+$, which
denotes a sum of types. The definition is straightforward, and
unsurprising to anyone who has ever done any generic programming: \[
(F \ssum G)\ L = F\ L + G\ L. \] That is, a labelled $(F \ssum G)$-shape is
either a labelled $F$-shape or a labelled $G$-shape.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia = struct 5 "F+G"
         ||||||
         strutX 1
         ||||||
         text' "="
         ||||||
         strutX 1
         ||||||
         ( struct 5 "F"
           ===
           text' "+"
           ===
           struct 5 "G"
         ) # centerY

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species sum}
    \label{fig:sum}
  \end{figure}

As the reader is invited to check, $(\ssum,\Zero)$ forms a commutative
monoid structure on species, up to species isomorphism.  That is, one
can define isomorphisms
\begin{align*}
&\cons{plusAssoc} : \impl{F, G, H : \Species} \to ((F \ssum G) \ssum H
\natiso F \ssum (G \ssum H)) \\
&\cons{zeroPlusL} : \impl{F : \Species} \to (\Zero \ssum F \natiso F) \\
&\cons{plusComm} : \impl{F, G : \Species} \to (F \ssum G \natiso G
\ssum F) \\
\end{align*}

\paragraph{Product}
The product of two species $F$ and $G$ consists of paired $F$- and
$G$-shapes, but with a twist: the label types $L_1$ and $L_2$ used for
$F$ and $G$ are not necessarily the same as the label type $L$
used for $(F \sprod G)$.  In fact, they must constitute a
partition of $L$, in the sense that their sum is isomorphic to $L$.
\begin{multline*}
(F \sprod G)\ L = (L_1, L_2 : \FinType) \times (L_1 + L_2 \iso L)
\\ \times F\ L_1 \times G\ L_2
\end{multline*}
The intuition here is that each label represents a unique ``location''
which can hold a data value, so the locations in the two paired
shapes should be disjoint.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia = struct 5 "F•G"
         ||||||
         strutX 1
         ||||||
         text' "="
         ||||||
         strutX 1
         ||||||
         ( struct 2 "F"
           ===
           strutY 0.2
           ===
           struct 3 "G"
         ) # centerY

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species product}
    \label{fig:product}
  \end{figure}

Another good way to gain intuition is to imagine indexing species not
by label types, but by natural number sizes.  Then it is easy to see
that we would have \[ (F \sprod G)_n = (n_1, n_2 : \N) \times (n_1 +
n_2 = n) \times F_{n_1} \times G_{n_2}, \] that is, an $(F \sprod
G)$-shape of size $n$ consists of an $F$-shape of size $n_1$ and a
$G$-shape of size $n_2$, where $n_1 + n_2 = n$.  Indexing by labels is
just a generalization (a \emph{categorification}, in fact) of this
size-indexing scheme, where we replace natural numbers with finite
types, addition with coproduct, multiplication with product, and
equality with isomorphism.

Finally, this definition highlights once again the fundamental
difference between \emph{container types} and \emph{labelled shapes}.
Given two functors representing container types, their product is
defined as $(F \times G)\ A = F\ A \times G\ A$---that is, an
$(F\times G)$-structure containing values of type $A$ is a pair of an
$F$-structure and a $G$-structure, both containing values of type $A$.
On the other hand, when dealing with labels instead of data values, we
have to carefully account for the way the labels are distributed among
the two shapes.

$(\sprod, \One)$ also forms a commutative monoid up to species
isomorphism.

\paragraph{Composition}

We may also define the \term{composition} of two species.
Intuitively, $(F \scomp G)$-shapes consist of a single top-level
$F$-shape, which itself contains labelled $G$-shapes in place of the
usual labels. \todo{needs a picture of some sort}

We represent this sort of nested shape by pairing an $F$-shape with a
vector of $G$-shapes, using a canonical labelling for the $F$-shape
and treating the vector as a mapping from this canonical label set to
labelled $G$-shapes. \todo{needs another picture} Finally, the label
type for the overall $(F \scomp G)$-shape is the sum of all the
individual label types used for the $G$-shapes.  Formally,
\begin{multline*}
 (F \scomp G)\ L = (k : \N) \times (\mathit{Ls} : \Vect\ k\ \Type) \\
 \times F\ (\Fin\ k) \times \sumTys\ (\map\ G\ \mathit{Ls})
\end{multline*}
where $\sumTys$ constructs the sum of a collection of types, and is defined by
\begin{spec}
  sumTys :  Vec n Type  ->   Type
  sumTys    []          =    undefined
  sumTys    (t::ts)     =    t + sumTys ts
\end{spec}
$k$ represents the size of the $F$-shape and hence also the number of
$G$-shapes.

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia = struct 6 "F∘G"
         ||||||
         strutX 1
         ||||||
         text' "="
         ||||||
         strutX 1
         ||||||
         drawSpT
         ( nd (text' "F")
           [ struct' 2 "G"
           , struct' 3 "G"
           , struct' 1 "G"
           ]
         ) # centerY

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species composition}
    \label{fig:composition}
  \end{figure}

$\scomp$, unlike $\ssum$ and $\sprod$, is not commutative: an $F$-shape
of $G$-shapes is quite different from a $G$-shape of $F$-shapes.  It
is, however, still associative (up to isomorphism), and in fact
$(\scomp, \X)$ forms a monoid up to species isomorphism.

\paragraph{Cartesian product}

As we saw earlier, the definition of the standard product operation on
species partitioned the set of labels between the two subshapes.
However, there is nothing to stop us from defining a different
product-like operation, known as \term{Cartesian product} which does
not partition the labels:\[ (F \scprod G)\ L = F\ L \times G\ L \]
This is, of course, the ``na\"ive'' version of product that one might
expect from experience with generic programming.

With labelled shapes, of course, this works very differently.  It is
important to remember that we still only get to specify a single
function of type $L \to A$ for the mapping from labels to data.  So
each label is still associated to only a single data value, but labels
can occur twice (or more) in an $(F \times G)$-shape.  This lets us
\emph{explicitly} model sharing, that is, multiple parts of the same
shape can all ``point to'' the same data.  In pure functional
languages such as Haskell or Agda, sharing is a (mostly) unobservable
operational detail; with a labelled structure we can directly model
and observe it.

\todo{illustration}

\todo{example}

$(\scprod, \E)$ forms a commutative monoid up to species isomorphism.

\paragraph{Cardinality restriction}

\todo{explain}

\begin{align*}
&\OfSize : \Species \to \N \to \Species \\
&\OfSize\ F\ n = \lam{L}{(\Fin n \iso L) \times F\ L}
\end{align*}

As is standard, we will use the notation $F_n$ as shorthand for
$\OfSize\ F\ n$.

We could also generalize to arbitrary collections of natural numbers,
as in
\begin{align*}
&\OfSize' : \Species \to (\N \to \Type) \to \Species \\
&\OfSize'\ F\ P = \lam{L}{(m : \N) \times P\ m \times (\Fin m \iso L)
  \times F\ L}
\end{align*}
The original $\OfSize$ can be recovered by setting $P\ m = (m \equiv
n)$.  However, $\OfSize'$ is difficult to compute with, since $P$ is
an opaque function.  In practice, $P\ m = (m \leq n)$ and $P\ m = (m
\geq n)$ (along with equality) cover the vast majority of cases we
care about, so as a practical tradeoff we can add explicit combinators
$\cons{OfSizeLT}$ and $\cons{OfSizeGT}$ representing these predicates,
abbreviated as $F_{\leq n}$ and $F_{\geq n}$ respectively.

\paragraph{Derivative and pointing}

The \term{derivative} is a well-known operation on shapes in the
functional programming community~\cite{holes etc.}, and it works in
exactly the way one expects on species.  That is, $F'$-shapes consist
of $F$-shapes with one distinguished location (a ``hole'') that
contains no data.  Formally, we may define

\[ F'\ L = (L' : \FinType) \times (L' \iso \TyOne + L) \times F\ L' \]

\todo{picture}

Note that a function of type $L \to A$ associates data to every label
in the underlying $F\ L'$ structure but one, since $L' \iso \TyOne +
L$.

A related, but constructively quite different operation is that of
\term{pointing}.  A pointed $F$-shape is an $F$-shape with a
particular label distinguished. \todo{picture} Formally,
\[ \pt{F}\ L = L \times F\ L. \]

The relationship bewteen pointing and derivative is given by the
isomorphism \[ \pt F \natiso \X \sprod F'. \]

\paragraph{Functor composition}

Just as a ``na\"ive'' product gave us some interesting structures with
value-level sharing, a ``na\"ive'' composition can do the same.  We
define the \term{functor product} of two species as follows:

\[ (F \fcomp G)\ L = F\ (G\ L) \]

Note that the label set given to $F$ is the set of \emph{all $(G\
  L)$-shapes}.  Giving $G$-shapes as labels for $F$ is the same as
$\scomp$; the difference is that with $\scomp$ the labels are
partitioned among all the $G$-shapes, but here the complete set of
labels is given to each $G$-shape.  This means that a particular label
could occur \emph{many} times in an $(F \fcomp G)$-shape, since it
will occur at least once in each $G$-shape, and the $F$-shape may
contain many $G$-shapes.

\todo{picture}

As an example, the species of simple directed graphs with labeled
vertices can be specified as \[ \mathcal{G} = (\E \sprod \E) \fcomp
(\X^2 \sprod \E), \] describing a graph as a subset ($\E \sprod \E$)
of the set of all ordered pairs chosen from the complete set of vertex
labels ($\X^2 \sprod \E$).

\todo{more examples}

$(\fcomp, \pt{\E})$ forms a (non-commutative) monoid up to species
isomorphism.

\section{Unlabelled structures}

\bay{``unlabelled'' is a terrible name for this, we need to come up
  with a better one.  In any case, the definition is equivalence
  classes of labelled structures.  Concretely, we always have to work
  with specific representatives of equivalence classes, and there is
  not always a nice way to choose a ``canonical'' representative.
  Instead, we can build relabelling into operations like zip so that
  some ``conversion'' is done in order to first relabel things so they
  match.  Such conversion is allowed when working with an equivalence
  class since it doesn't matter which representative we use.}

\section{Labelled Structures in Haskell}
\label{sec:haskell}

\todo{
  Describe our implementation.  Note that actually compiling such
  things to efficient runtime code is future work.
}

\todo{be sure to discuss recursion.}

\section{Programming with Labelled Structures}
\label{sec:programming}

\todo{
  Give some examples of using our implementation.
  e.g. $n$-dimensional vectors.
}

\subsection{Arrays}
\label{sec:arrays}

As an extended example and a good way to explore some of the
combinators which are possible, we present a framework for programming
with (arbitrary-dimensional) \emph{arrays}.

\todo{Define array: n-dimensional, indexed data.  Not necessarily the
  same as a *matrix* (which has additional meaning attached to it).}

\todo{The following text is just pasted in from an email, needs some
  major editing.}

For some structures (namely, ``regular'' structures) there is a
canonical labeling which is based on the structure.  We can use that
to push structure back and forth between the shapes and the labels.

So for suitable |f| we should have
\begin{spec}
canonicalize :: Suitable f => Sp f l a -> (Sp f (Path f) a, l <-> Path f)
\end{spec}

That is, we can relabel a structure, using paths into |f| as canonical
labels (and along the way we can also find out how the old labels
match up with the new canonical ones).

Now, the problem with |(Sp f (Path f) a)| is that we've duplicated
structure in both the shape and the labels.  |canonicalize| doesn't
directly have a sensible inverse because given something of type |(Sp f
(Path f) a)| we have no guarantee that the labels match the structure.

So, we have a function
\begin{spec}
forgetShape :: Sp f l a -> Sp E l a
\end{spec}
which forgets the shape.  Of course, the labels may have a lot of
structure so this may or may not actually lose information.  We can
then go backwards:
\begin{spec}
reconstitute :: Sp E (Path f) a -> Sp f (Path f) a
\end{spec}
We have the law
\begin{spec}
forgetShape . reconstitute = id
\end{spec}
and also, we can define
\begin{spec}
unCanonicalize :: (Sp f (Path f) a, l <-> Path f) -> Sp f l a
unCanonicalize (sp, i) = relabel (from i) (reconstitute . forgetShape $ sp)
\end{spec} %$
which is left inverse to |canonicalize|.

This lets us go back and forth between different views of data.  Some
operations are ``structural'', \ie operate on nontrivial shapes
(\eg matrix multiplication) whereas some (\eg transpose) are best
expressed as operations on structured labels.

The shape of 2D arrays, for example, is $L_m \comp L_n$ (if we consider 2D
arrays as a data structure where the ordering of elements is
significant).  But $Path(L_m \comp L_n) \sim (Fin m, Fin n)$, so we can convert
between $(Sp (L_m \comp L_n) l a)$ and $(Sp E (Fin m, Fin n) a)$.


\section{Related Work}
\label{sec:related}

\begin{itemize}
\item containers, naturally
\item shapely types
\item HoTT?
\end{itemize}

\section{Conclusion}
\label{sec:conclusion}


%\bibliographystyle{plainnat}
%\bibliography{paper}

\end{document}
