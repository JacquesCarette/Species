%% -*- LaTeX -*-

\documentclass{llncs}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%format sumTys = "\cons{sumTys}"
%format <->    = "\iso"
%format compP  = "\cons{compP}"

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

% \newtheorem{theorem}{Theorem}
% \newtheorem{proposition}[theorem]{Proposition}
% \newtheorem{lemma}[theorem]{Lemma}

% \theoremstyle{definition}
% \newtheorem{definition}[theorem]{Definition}

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
\DeclareMathOperator{\LStr}{LStr}
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

% \authorinfo{Brent A. Yorgey \\ Stephanie Weirich}
% {Dept. of Computer and Information Science\\ The University of Pennsylvania\\
% Philadelphia, Pennsylvania, USA}
% {\{byorgey,sweirich\}@@cis.upenn.edu}

% \authorinfo{Jacques Carette}
% {Dept. of Computing and Software\\ McMaster University\\
% Hamilton, Ontario, Canada}
% {carette@@mcmaster.ca}

\author{Brent A. Yorgey\inst{1} \and Stephanie Weirich\inst{1} \and
  Jacques Carette\inst{2}}

\institute{Dept. of Computer and Information Science\\
The University of Pennsylvania\\
Philadelphia, Pennsylvania, USA
\and
Dept. of Computing and Software\\ McMaster University\\
Hamilton, Ontario, Canada}

\maketitle

\begin{abstract}

\todo{Abstract goes here.}

\end{abstract}

% \category{D.3.2}{Programming Languages}{Applicative (functional) languages}

% \terms
% Languages, Types

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
\item a (total) function $m : L \to A$ which maps labels to data values.
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
we use a subscript, as in $f_{\N}\ 3$.  Free type variables should be
understood as implicit arguments, for example, the type $A \to A$ is
shorthand for $\impl{A:\Type} \to A \to A$.

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

Formally, we may define families of labelled structures as follows.
\begin{align*}
   &\LStr : \Species \to \FinType \to \Type \to \Type \\
   &\LStr\ F\ L\ A = F\ L \times (L \to A)
\end{align*}
that is, a labelled structure over the species $F$, a
constructively finite type $L$ of labels, and a type $A$ of
data consists simply of
\begin{itemize}
\item a shape of type $F\ L$, \ie\ an $L$-labelled $F$-shape, and
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
associated introduction form(s), for both ``bare'' shapes and for
labelled structures.  We discuss eliminators in~\pref{sec:elim}.

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
  $\Fin\ 0$, that is, \[ \top : \One\ (\Fin\ 0). \] In a further abuse
  of notation we can also use $\top$ to denote an introduction form
  for labelled $\One$-structures, \[ \top : \LStr\ \One\ (\Fin\ 0)\
  A. \]

  Introducing a canonical label type will be standard for introduction
  forms; other label types may be obtained via relabelling.

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
  \[ \cons{x} : \X\ (\Fin\ 1). \]  To introduce an $\X$-structure, one
  must provide the single value of type $A$ which is to be stored in
  the single location: \[ \cons{x} : A \to \LStr\ \X\ (\Fin\ 1)\ A. \]

\paragraph{Sets}
The species of \emph{sets}, denoted $\E$, is defined by \[ \E\ L =
\TyOne. \] That is, there is a single $\E$-shape for every label type.
Intuitively, $\E$-shapes impose no structure whatsoever; that is, an
labelled $\E$-shape can be thought of simply as a \emph{set} of labels.

Note that if $\E$-shapes are sets, then labelled
$\E$-\emph{structures} ($\E$-shapes plus mappings from labels to data)
are \emph{bags}: any particular data element may occur multiple times
(each time associated with a different, unique label).

$\E$-shapes also have a trivial introduction form, $\cons{e} : \E\ L$,
along with a corresponding introduction form for $\E$-structures
which simply requires the mapping from labels to values: \[ \cons{e} :
(L \to A) \to \LStr\ \E\ L\ A. \]

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
\todo{need to explain what these pictures mean at some point, and make
  sure each picture is referenced from the text.}

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

As expected, there are two introduction forms for $(F \ssum G)$-shapes
and -structures:
\begin{align*}
&\cons{inl} : F\ L \to (F \ssum G)\ L \\
&\cons{inr} : G\ L \to (F \ssum G)\ L \\
&\cons{inl} : \LStr\ F\ L\ A \to \LStr\ (F \ssum G)\ L\ A \\
&\cons{inl} : \LStr\ G\ L\ A \to \LStr\ (F \ssum G)\ L\ A \\
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

One introduces a labelled $(F \sprod G)$-shape by pairing a labelled $F$-shape and a
labelled $G$-shape, using a canonical label set formed as the
coproduct of the two label types:
\begin{align*}
  &\langle - , - \rangle : F\ L_1 \to G\ L_2 \to (F \sprod G)\ (L_1 +
  L_2) \\
  &\langle - , - \rangle : \LStr\ F\ L_1\ A \to \LStr\ G\ L_2\ A \to
  \LStr\ (F \sprod G)\ (L_1 +
  L_2)\ A
\end{align*}

$(\sprod, \One)$ also forms a commutative monoid up to species
isomorphism.

\paragraph{Composition}

We may also define the \term{composition} of two species.
Intuitively, $(F \scomp G)$-shapes consist of a single top-level
$F$-shape, which itself contains labelled $G$-shapes in place of the
usual labels, as illustrated in~\pref{fig:composition}.

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

Unlike the shape constructions we've seen up to now, the space of
introduction forms for composition structures is actually quite
interesting.  We will not separately consider introduction forms for
composition shapes, but study introduction forms for composition
structures directly.

At the simplest end of the spectrum, we can define |compP| as follows,
which is a sort of cartesian product, copying the provided $G$
structure into every location of the $F$ structure and pairing up
their labels and data:
\begin{multline*}
  \cons{compP} : \LStr\ F\ L_1\ A \to \LStr\ G\ L_2\ B \\ \to \LStr\ (F
  \scomp G)\ (L_1 \times L_2)\ (A \times B)
\end{multline*}

\todo{explain this better, and add an illustration of |compP|}

\todo{monoidal something-or-other. Like Applicative.  So we can
  equivalently have:}

\begin{multline*}
  \cons{compA} : \LStr\ F\ L_1\ (A \to B) \to \LStr\ G\ L_2\ A \\ \to \LStr\ (F
  \scomp G)\ (L_1 \times L_2)\ B
\end{multline*}

\todo{Can also have something like monadic join:}

\begin{multline*}
  \cons{compJ} : \LStr\ F\ L_1\ (\LStr\ G\ L_2\ A) \to \LStr\ (F \scomp
  G)\ (L_1 \times L_2)\ A
\end{multline*}

\todo{And finally, a dependent version something like monadic
  bind. Note that $L_2 : L_1 \to \FinType$ is allowed to depend on $L_1$.}

\begin{multline*}
  \cons{compB} : \LStr\ F\ L_1\ \TyOne \to ((l : L_1) \to \LStr\ G\
  (L_2\ l)\ A) \\ \to \LStr\ (F \scomp G)\ ((l : L_1) \times L_2\ l)\ A
\end{multline*}

\todo{add some pictures for the above}

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

To introduce a Cartesian product shape, one simply pairs two shapes on
the same set of labels.  Introducing a Cartesian product structure is
more interesting. One way to do it is to overlay an additional shape
on top of an existing structure: \[ \cons{cprodL} : F\ L \to \LStr\ G\ L\ A
\to \LStr\ (F \scprod G)\ L\ A. \] There is also a corresponding
$\cons{cprodR}$ which combines an $F$-structure and a $G$-shape.
\todo{picture}

$(\scprod, \E)$ forms a commutative monoid up to species isomorphism.

\paragraph{Cardinality restriction}

Another important operation on species is \term{cardinality
  restriction}, which simply restricts a given species to only have
shapes of certain sizes.  For example, if $\L$ is the species of
lists, $\L_3$ is the species of lists with length exactly three, and
$\L_{\geq 1}$ is the species of non-empty lists.  We can formalize a
simple version of this, for restricting only to particular sizes, as
follows:

\begin{align*}
&\OfSize : \Species \to \N \to \Species \\
&\OfSize\ F\ n = \lam{L}{(\Fin n \iso L) \times F\ L}
\end{align*}

As is standard, we use the notation $F_n$ as shorthand for
$\OfSize\ F\ n$.

We could also generalize to arbitrary predicates on natural numbers,
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

The introduction form for $\OfSize$ is simple enough,
\[ \cons{sized} : \LStr\ F\ L\ A \to \LStr\ (\OfSize\ F\ ||L||)\ L\ A, \]
where $||L||$ denotes the size of $L$ ($L$ is a $\FinType$ and
therefore has a natural number size).

\todo{intro forms for $\cons{OfSizeLT}$ and $\cons{OfSizeGT}$?}

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

To introduce a derivative structure, we require an input structure
whose label type is already in the form $\TyOne + L$: \[ \cons{d} :
\LStr\ F\ (\TyOne + L)\ A \to \LStr\ F'\ L\ A. \]

A related, but constructively quite different operation is that of
\term{pointing}.  A pointed $F$-shape is an $F$-shape with a
particular label distinguished. \todo{picture} Formally,
\[ \pt{F}\ L = L \times F\ L. \]
Introducing a pointed structure requires simply specifying which label
should be pointed: \[ \cons{p} : L \to \LStr\ F\ L\ A \to \LStr\
(\pt{F})\ L\ A. \]

The relationship bewteen pointing and derivative is given by the
isomorphism \[ \pt F \natiso \X \sprod F'. \] \todo{say more about
  this?}

\paragraph{Functor composition}

Just as a ``na\"ive'' product gave us some interesting structures with
value-level sharing, a ``na\"ive'' composition can do the same.  We
define the \term{functor product} of two species as follows:
\[ (F \fcomp G)\ L = F\ (G\ L). \]

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

\todo{introduction form(s)?}

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

What is an array?  One typically thinks of arrays as $n$-dimensional
grids of data, like
\[
\begin{bmatrix}
5.6 & 5.9 & 5.4 & 0.7\\
0.1 & 7.4 & 2.1 & 5.9\\
1.9 & 2.4 & 7.9 & 7.5
\end{bmatrix}
\]
That is, within the framework of labelled structures, one would think
of a two-dimensional array as a \emph{two-dimensional grid shape}
paired with some data.
\[
\begin{bmatrix}
\square & \square & \square & \square\\
\square & \square & \square & \square\\
\square & \square & \square & \square
\end{bmatrix}
+ 5.6, 5.9, 5.4, \dots
\]
Under this view the particular labels used to match up locations and
data do not matter very much (which is why labels are omitted in the
picture above).

However, there is another way to view arrays as labelled structures:
we can view them as consisting of labelled \emph{bag} shapes (that is,
shapes with no structure whatsoever), with the $n$-dimensional
structure instead inherent in the particular type of labels used.  For
example, a two-dimensional matrix can be viewed as a labelled bag
structure where the labels are elements of some product type.

This view has several advantages: first, by using label types with
other sorts of structure we can easily obtain generalizations of the
usual notion of arrays. Second, it lends itself particularly well to
index-oriented operations: for example, transposing a two-dimensional
array is just a call to |relabel|.  One might imagine being able to
easily optimize away such label-based operations (whereas an
implementation of transposition as a structure-based operation on grid
shapes would be much more difficult to work with).

\bay{The usual eliminators are useless on
  arrays-as-bags-of-structured-labels, because they are not allowed to
  take into account any structure on labels.  So why are we justified
  in taking label structure into account for various operations on
  arrays?  I feel strongly that we are/should be justified but I am
  not quite sure yet of the right way to explain it.  It has to
  do specifically with using a bag shape.  If we use some nontrivial
  shape and \emph{also} have nontrivial structure on the labels then
  there is potential for the two structures to ``get out of sync''.
  We start to address some of this in the next section.}

% So I went to try to implement some of this yesterday.  I started out
% by trying to implement

%   unComp :: Sp (Comp f g) (l1,l2) a -> Sp f l1 (Sp g l2 a)

% I tried writing out an implementation on paper and was having real
% trouble.  Once again the types seemed to be indicating that I was
% doing something wrong.  After some deeper reflection I have come to
% realize that a function with this type cannot possibly exist!

% Jacques, you were actually right: (E . E) is not the right shape for
% matrices.  The problem is that it allows ragged matrices.  Having
% something of type Sp (E.E) (l1,l2) does not actually guarantee that we
% have l1-many rows each labeled by l2: all we know is that there are
% l1xl2 many entries *in total*, but they can be distributed in weird
% ways.

% So one idea would be to use something like (E_m . E_n) as the shape of
% mxn matrices, as Jacques originally suggested.  That solves the
% problem of ragged matrices, but actually the problem goes deeper than
% that: given an (E_m . E_n) (l1,l2)-structure, we still can't take it
% apart coherently because we don't know labels are distributed in a way
% that matches the structure.  e.g. we could have

%    { { (1,2), (2,1), (2,3) }
%    , { (2,2), (1,1), (1,3) }
%    }

% which is incoherent since the (1,x) labels are not all contained in
% a single row, and so on.

% I think the right solution is to just use E as the shape of all
% (n-dimensional) matrices, with all the structure in the labels.  In
% other words, we don't try to impose any ideas about how a matrix is
% "structured" unless we need the structure for some reason. E.g. to
% construct a 2D matrix we first use composition:

%   Sp E l1 a -> Sp E l2 a -> Sp (E . E) (l1,l2) a

% But instead of leaving it like that, we now use a "reshape" operation
% along with the fact that we have a nice "join" operation (E.E) -> E to get

%   Sp E (l1,l2) a

% Now doing things like transposition really is just a relabeling (note
% that the version of transposition I implemented before had the problem
% that it changed the labels without doing any restructuring, so the
% labels no longer corresponded to the structure).  We can (I think)
% implement an "uncompose" operation of type

%   Sp E (l1,l2) a -> Sp E l1 (Sp E l2 a)

% by just splitting up into subsets according to the label structure.
% However note that this is specialized to E: we certainly can't do this
% in general for arbitrary shapes.  Though I'm sure it can be
% generalized in some way, but I haven't thought carefully yet about
% what that might look like.

\subsection{Zipping}
\label{sec:zipping}

One natural operation on arrays of the same size is to \term{zip}
them, applying some operation to their corresponding elements
pointwise and producing a new array.

\todo{talk about |zip|: can zip two labelled structures with bag
  shapes and matching label types.  But to zip structurally we need
  ``unlabelled'' structures so we can force the labels to match up via
  the structures.}

% Now, on to zipping in general.  The problem is that zipping two
% labelled structures where the structures are nontrivial is
% nonsensical: we must be able to match up both the structures *and* the
% labels, but we cannot do both in general.  Ultimately I think the real
% problem here is that we usually don't work directly with labelled
% structures but with unlabelled, that is, equivalence classes of
% labelled structures.  For *regular* unlabelled structures (i.e. ones
% with no symmetry) we can then zip because the structure itself gives
% us canonical labels---as labels we can use the type of "paths" into
% the structure.  So then we are back to matching up labels, but they
% are guaranteed to match the structure.

% However I am really not sure how to talk about unlabelled species
% within our framework.  For a regular species S we can sort of fake it
% by using E (Path S), i.e. labelled bags where (Path S) is the type of
% paths into S.  But that's not all that nice and I'm not even convinced
% it's really the same thing.

% Hmm, now that I think of it, perhaps the idea for unlabelled
% structures would just be that the system is allowed to permute the
% labels at any time, and you the user are not supposed to care because
% you are working with an equivalence class instead of with a concrete
% labelling.  I suppose this could be enforced by existentially
% quantifying over the labels or something like that.  So a zip on
% "unlabelled" structures (urgh, unlabelled is a really bad name!) gets
% to first permute the labels so they match up before doing the zip.



% I've now been thinking about how to compute the sum of two such
% matrices.  We evidently need some way to be able to "zip" two shapes
% together.  So I made a class

%   class Zippy f where
%     fzip :: f l -> f l -> f l

% Instances for One, X, and E are easy enough to write (because there is
% only one shape of each type).  I was expecting to be able to write an
% instance for products but not for sums.  But I got to

%   instance (Zippy f, Zippy g) => Zippy (f * g) where
%     fzip (Prod f1 g1 pf1) (Prod f2 g2 pf2) = ?

%   where
%     f1 :: f l11
%     g1 :: g l12
%     pf1 :: Either l11 l12 <-> l
%     f2 :: f l21
%     g2 :: g l22
%     pf2 :: Either l21 l22 <-> l

% can you use those to construct something of type (f * g) l?  Of course
% we could just cheat and return one or the other Prod, but that's
% definitely cheating since we wouldn't even be using the fact that f
% and g are Zippy.  The problem is that the labels l might not have been
% partitioned between f and g in the same way, so there's no guarantee
% we can do any recursive zipping.

% Of course, if product doesn't even work then composition seems right
% out.  But everyone knows that you can zip matrices of the same size.
% So what gives?  I guess there's actually something special going on
% with E.  E o E  should be Zippy even though we can't say in general
% that (f o g) is Zippy when f and g are.  But I'm not sure how to make
% this precise.


\todo{explain matrix multiplication.  Need to first finish writing
  about introduction forms for composition.}

% Here's how matrix product works.  Recall that 2-dimensional matrices
% have the shape (E . E), where . represents composition.  So I will
% abbreviate the type of 2D matrices containing elements of type a and
% labeled with pairs from the set (Fin m, Fin n) as (E.E) (m,n) a.  Now
% suppose we want to multiply two matrices of types

%   (E.E) (m,p) a
%   (E.E) (p,n) a

% assuming a suitable ring structure on the type a.  First we transpose
% the second matrix (by relabeling) to get (E.E) (n,p) a.  Now we
% "decompose" both to get

%   E m (E p a)
%   E n (E p a)

% This decomposition step corresponds to shifting from viewing them as
% 2D matrices to viewing them as 1D matrices of 1D matrices
% (i.e. collections of rows).  We now compose these two (using
% e.g. compA), i.e. we pair up rows from the two matrices in all
% possible ways, resulting in something of type

%   (E.E) (m,n) (E p a, E p a)

% Finally we zip the rows together,

%   (E.E) (m,n) (E p (a,a))

% multiply the resulting pairs,

%   (E.E) (m,n) (E p a)

% and sum over the size-p sets,

%   (E.E) (m,n) a.

% This is all much clearer with the aid of the pictures we scribbled on
% my paper placemat at New Delhi, but hopefully it makes a bit of
% sense.  I hope to have some code to show you soon as well. =)

% Note also that the above is actually not specific to 2D matrices.
% More generally, n-dimensional matrices have shape E^n.  To multiply a
% j-D matrix by a k-D matrix along a certain axis, we first reassociate
% and relabel to bring the axes we want to multiply to the end (their
% size must match, of course):

%   (E^(j-1) . E) (dims1, p) a
%   (E^(k-1) . E) (dims2, p) a

% dims1 and dims2 can be arbitrarily associated (n-1)-tuples.  We can
% then perform all the above operations, resulting in something of type

%   (E^(j+k-2)) (dims1,dims2) a .

\subsection{Moving structure between shapes and labels}
\label{sec:moving-structure}

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
