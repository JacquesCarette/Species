\documentclass[9pt,preprint,authoryear]{sigplanconf}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{../species}

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
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

\DeclareMathOperator{\map}{map}
\DeclareMathOperator{\sumTys}{sumTys}

\newcommand{\mor}{\stackrel{\bullet}{\rightarrow}}
\newcommand{\natiso}{\stackrel{\bullet}{\iso}}

\newcommand{\ssum}{\oplus}
\newcommand{\sprod}{\odot}
\newcommand{\scomp}{\circledcirc}

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
of container shapes and the data stored in those shapes.  Labels
provide the missing link between shapes and data, allowing one to
specify which data goes where.

Informally, a \term{labelled structure} is specified by:
\begin{itemize}
\item a finite type of labels $L$;
\item a type of data elements $A$;
\item some sort of ``shape'' containing each label from $L$ exactly
  once; and
\item a function $v : L \to A$ which maps labels to data values.
\end{itemize}
See~\pref{fig:labelled-structure-example} for an abstract example.  A
\emph{family} of labelled structures refers to a class of structures
parameterized over the label type $L$ and data type $A$.

\begin{figure}
  \centering
\begin{diagram}[width=200]
import Graphics.SVGFonts.ReadFont
import Diagrams.Points

mark = named ()

mkL n = text' (show n) <> (circle 0.8 # mark)

text' s = (stroke $ textSVG' (TextOpts s lin2 INSIDE_H KERN False 1 1)) # fc black # lw 0

drawLabels = centerByMarks
           . cat' (unitX # rotateBy (-1/3)) myCatOpts
           . map (hcat' myCatOpts . map mkL)
  where
    myCatOpts = with {catMethod = Distrib, sep = 2.5}

centerByMarks = withNameAll () $ \ss ->
  let p = centroid (map location ss)
  in  moveOriginTo p

labs = drawLabels [[2],[1,4],[3,0,5]]

shape = triangle (width (labs :: D R2) + 2.5)

mapping = centerY . vcat' with {sep = 0.3} $ zipWith mkMapping [0..5] "SNAILS"
  where
    mkMapping i c = mkL i .... hrule 1 .... (text' (show c) <> strutX 1)

dia = ((labs <> shape) # centerY ... strutX 5 ... mapping)
    # centerXY # pad 1.1

infixl 6 ...
infixl 6 ....
(...) = (||||||)
x .... y = x ... strutX 0.5 ... y
\end{diagram}
%$
  \caption{A labelled structure with six labels}
  \label{fig:labelled-structure-example}
\end{figure}

\bay{another, perhaps better, way to say "contain each label once":
  the size of a shape is determined by the size of the label set.}

Note that shapes must contain each label exactly once, but the
function $L \to A$ need not be injective. As illustrated in
\pref{fig:labelled-structure-example}, it is perfectly valid to have
the same value of type $A$ occurring multiple times, each matched to a
different label.  The requirement that shapes contain all the labels,
with no duplicates, may seem overly restrictive; we will have more to
say about this later.  The notion of ``shape'' is also left vague for
now; a precise definition will be given in \todo{where?}.

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

% We want to think of each labeled structure as \emph{indexed by} its
% set of labels (or, more generally, by the \emph{size} of the set of
% labels).  We can accomplish this by a mapping from label sets to all
% the structures built from them, with some extra properties to
% guarantee that we really do get the same family of structures no
% matter what set of labels we happen to choose.

\subsection{Species, set-theoretically}
\label{sec:set-species}

We begin with a standard set-theoretic definition of species
\cite{Joyal, BLL} (we will upgrade to a \emph{type}-theoretic
definition in \pref{sec:constructive-species}).

\begin{definition}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $L$ (of \term{labels}) to a finite set
  $F(L)$ (of \term{shapes}), and
\item sends any bijection on finite sets $\sigma : L \iso L'$ (a
  \term{relabelling}) to a function $F(\sigma) : F(L) \to F(L')$
  (illustrated in \pref{fig:relabelling}),
\end{itemize}
satisfying the following functoriality conditions:
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

Note that in the combinatorial literature, elements of $F(L)$ are
usually called ``$F$-structures'' rather than ``$F$-shapes''.
To a combinatorialist, labelled shapes are themselves the primary
objects of interest; however, in a computational context, we must be
careful to distinguish between labelled structures (which have data
associated with the labels) and bare labelled shapes (which do not).

Here we see that the formal notion of ``shape'' is actually quite
broad, so broad as to make one squirm: a shape is just an element of
some arbitrary set!  In this context our informal insistance from the
previous section that a shape ``contain each label exactly once'' is
completely meaningless, because there is no sense in which we can say
that a shape ``contains'' labels.

In practice, however, we are interested not in arbitrary species but
in ones built up algebraically from a set of primitives and
operations.  In that case the corresponding shapes will have more
structure as well. Before we get there, however, we need to give the
definition of species a firmer computational basis.

\subsection{Species, constructively}
\label{sec:constructive-species}

The foregoing set-theoretic definition of species is perfectly
serviceable in the context of classical combinatorics, but in order to
use it as a foundation for data structures, it is useful to first
``port'' the definition from set theory to constructive type theory.

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
when $x$ does not appear free in $B$.  We write $\impl A \to B$ for
the type of functions taking $A$ as an \emph{implicit} argument, and
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

\subsection{Species, algebraically}
\label{sec:algebraic}

We now return to the observation from \pref{sec:set-species} that we
do not really want to work directly with the definition of species,
but rather with an algebraic theory. \todo{say a bit more}

\paragraph{Zero}
  The \emph{zero} or \emph{empty} species, denoted $\Zero$, is the
  unique species with no shapes whatsoever, defined by its action on
  finite types and bijections as
  \begin{align*}
  \Zero\ L &= \TyZero \\
  \Zero\ \sigma &= \id_\TyZero
  \end{align*}
  \bay{Say more here?}

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

\paragraph{Singleton}
  The \emph{singleton} species, denoted $\X$, is defined by
  \[ \X\ L = \TyOne \iso L, \] that is, an $\X$-shape is just a proof that
  $L$ has size $1$.  Again, if there is such a proof, there is only
  one.  Unlike $\One$, we may also think of an $\X$-shape as
  ``containing'' a single label of type $L$, which we may recover by
  applying the isomorphism to $\unit$.

  Note that once again the definition is ``obviously'' functorial; we
  may syntactically replace $L$ by $\sigma$ to obtain \[ \X\ \sigma =
  \top \iso \sigma. \]  This will remain true for most \bay{all?} of the
  definitions given from here on. \bay{But we will explicitly discuss
    it when it is not obvious?}

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

\todo{Note that a lot of the power of the theory for combinatorics
  comes from homomorphisms to rings of formal power series; we won't
  use that in this paper.}

We have now seen four primitive species: \Zero, \One, \X, and \E.  It
turns out that each of them is the unit for a monoidal operation on
species; we will look at each of these in turn.  Before we get there,
however, we need to take a brief detour to discuss isomorphism of
species.

\subsection{Species isomorphism}
\label{sec:species-iso}

Since species are functors, a \term{morphism} between species is a
natural transformation.  Spelling this out, the type of species
morphisms is given by
\begin{align*}
  &- \mor - : \Species \to \Species \to \Type \\
  &F \mor G = (\varphi : \impl{L : \FinType} \to F\ L \to G\ L)
  \times \Natural\ \varphi
\end{align*}
where $\Natural\ \phi$ is the proposition which states that $\phi$ is
\term{natural}, that is, the following diagram commutes for all $L :
\FinType$:

\centerline{
  \xymatrix{
    F\ L \ar[d]_{\varphi_L} \ar[r]^{F\ \sigma} & F\ L' \ar[d]^{\varphi_{L'}} \\
    G\ L                    \ar[r]_{G\ \sigma} & G\ L'
  }
}

Intuitively, $\varphi$ is natural if it does not depend on the type of
the labels, that is, it acts uniformly for all choices of label set:
it does not matter whether one first relabels an $F$-shape and then
applies $\varphi$, or applies $\varphi$ first and later relabels.

An \term{isomorphism} between species, denoted $F \natiso G$, is a
pair of inverse morphisms.\bay{explain in more detail?}

Species isomorphism preserves all the interesting \emph{combinatorial}
properties of species; hence in the combinatorics literature
everything is always done up to isomorphism. However, isomorphism does not
necessarily preserve all the \emph{computational} properties we might
care about.  For example, \todo{example}.

It is worth noting that a pair of ``bare'' inverse morphisms, without
naturality, constitute what is termed an \term{equipotence} between
two species.  An equipotence preserves the \emph{number} of shapes of
each size, but it does not necessarily preserve the structure of those
shapes.  For example, \todo{example}.  Equipotences are of interest to
combinatorialists, but they do not seem to be of much use in the
service of computation, so we will not consider them further.

\subsection{Species operations}
\label{sec:species-ops}

\paragraph{Sum}
Given two species $F$ and $G$, we may form their sum. We use $\ssum$
for the sum of two species to distinguish it from $+$, which denotes a
sum of types. The definition is straightforward, and unsurprising to
anyone who has ever done any generic programming: \[ (F \ssum G)\ L =
F\ L + G\ L. \] That is, an $(F \ssum G)$-shape is either an
$F$-shape or a $G$-shape.

As the reader is invited to check, $\Zero$ is the identity element for
$\ssum$ up to species isomorphism.  That is, we can define
\[ zeroPlusL : \impl{F : \Species} \to (\Zero \ssum F) \natiso F \]
and also a similar isomorphism $zeroPlusR$.

\paragraph{Product}
The product of two species $F$ and $G$ consists of paired $F$- and
$G$-shapes, but with a twist: the label types $L_1$ and $L_2$ passed
to $F$ and $G$ are not necessarily the same as the label type $L$
which is passed to $(F \sprod G)$.  In fact, they must constitute a
partition of $L$, in the sense that their sum is isomorphic to $L$.
\begin{multline*}
(F \sprod G)\ L = (L_1, L_2 : \FinType) \times (L_1 + L_2 \iso L)
\\ \times F\ L_1 \times G\ L_2
\end{multline*}
The intuition here is that if an $(F \sprod G)$-shape is to contain
each label from $L$ exactly once, then the labels must be divvied up,
some going into the $F$-shape and some into the $G$-shape.

\todo{$\One$ is identity for $\sprod$.}

\paragraph{Composition}

\begin{multline*}
 (F \scomp G)\ L = (n : \N) \times (\mathit{Ls} : \Vect\ n\ \Type) \\
 \times F\ (\Fin\ n) \times \sumTys\ (\map\ G\ \mathit{Ls})
\end{multline*}
where $\sumTys$ is defined by
\todo{fix typesetting}
\begin{spec}
  sumTys :  Vec n Type  ->   Type
  sumTys    []          =    \bot
  sumTys    (t:ts)      =    t + sumTys ts
\end{spec}

\paragraph{Cartesian product}

\[ (F \scprod G)\ L = F\ L \times G\ L \]

\paragraph{Cardinality restriction}

\paragraph{Derivative and pointing}

\paragraph{Functor composition}

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

\todo{formal intro and elim forms for labelled structures? operations
  on labelled structures?}

\todo{how formal do we want/need to make this?}

\section{Labelled Structures in Haskell}
\label{sec:haskell}

\todo{
  Describe our implementation.  Note that actually compiling such
  things to efficient runtime code is future work.
}

\section{Programming with Labelled Structures}
\label{sec:programming}

\todo{
  Give some examples of using our implementation.
  e.g. $n$-dimensional vectors.
}

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
