%% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass[adraft,copyright,creativecommons]{eptcs}
\providecommand{\event}{MSFP 2014}
\usepackage{breakurl}
\usepackage{natbib}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

%format <->    = "\iso"
%format compP  = "\compP"
%format compA  = "\compA"
%format <*>    = "<\!\!*\!\!>"

%format le_intro = "\lab{\cons{e}}"

%format LStr (f) (l) (a) = "\LStr{" f "}{" l "}{" a "}"

%format pi = "\pi"
%format pi1
%format pi2
%format n1
%format n2
%format sub1
%format sub2
%format v1
%format v2
%format i1
%format i2
%format s1
%format s2

%format inr = "\inr"
%format inl = "\inl"
%format outr = "\outr"
%format outl = "\outl"

%format inv(a) = a "^{-1}"

%format sumN = sum "_\N"
%format sumTy = sum "_\Type"

%format allocateV = allocate "_V"
%format mapV = map "_V"
%format foldV = fold "_V"
%format appendV = append "_V"
%format concatV = concat "_V"
%format sumV = sum "_V"

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

\usepackage{../species}

\usepackage{amsthm}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
% \usepackage{proof}
% \usepackage{comment}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}

% \usepackage{mathpazo}  % Looks nicer but doesn't conform to EPTCS style

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
\usepackage[outputdir=diagrams,backend=ps,extension=eps]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

% Use sans-serif for math operators
\DeclareSymbolFont{sfoperators}{OT1}{cmss}{m}{n}
\DeclareSymbolFontAlphabet{\mathsf}{sfoperators}

\makeatletter
\def\operator@@font{\mathgroup\symsfoperators}
\makeatother

\newcommand{\lam}[2]{\lambda #1 . #2}

\newcommand{\iso}{\simeq}
\newcommand{\mkIso}{\rightleftharpoons}

% \newcommand{\impl}[1]{\ensuremath{\{#1\}}} % implicit arguments
\newcommand{\impl}[1]{\ensuremath{(#1)}}   % not notating implicit
                                           % arguments at the moment
\newcommand{\defn}{\vcentcolon\equiv}

\newcommand{\TyZero}{\ensuremath{\bot}}
\newcommand{\TyOne}{\ensuremath{\top}}
\newcommand{\unit}{\ensuremath{\star}}

\newcommand{\cons}[1]{\ensuremath{\mathsf{#1}}}

\newcommand{\inl}{\cons{inl}}
\newcommand{\inr}{\cons{inr}}
\newcommand{\outl}{\cons{outl}}
\newcommand{\outr}{\cons{outr}}

\newcommand{\Type}{\ensuremath{\mathcal{U}}}
\newcommand{\FinType}{\ensuremath{\Type_{\text{Fin}}}}

\newcommand{\size}[1]{\ensuremath{||#1||}}

\newcommand{\lab}[1]{\ensuremath{\left\langle #1 \right\rangle}}

\DeclareMathOperator{\Species}{Species}
\DeclareMathOperator{\RegSpecies}{RegSpecies}
\DeclareMathOperator{\Regular}{Regular}
\DeclareMathOperator{\Fin}{Fin}
\DeclareMathOperator{\Finite}{Finite}
\DeclareMathOperator{\NatZ}{O}
\DeclareMathOperator{\NatS}{S}
\DeclareMathOperator{\FinZ}{fO}
\DeclareMathOperator{\FinS}{fS}
\DeclareMathOperator{\VectOp}{Vec}
\DeclareMathOperator{\id}{id}
\DeclareMathOperator{\shapes}{shapes}
\DeclareMathOperator{\relabel}{relabel}
\DeclareMathOperator{\Natural}{Natural}
\DeclareMathOperator{\OfSize}{OfSize}
\DeclareMathOperator{\OfSizeLTE}{OfSizeLTE}
\DeclareMathOperator{\OfSizeGTE}{OfSizeGTE}

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

\newcommand{\LStr}[3]{\langle #1 \rangle_{#2}(#3)}

\newcommand{\compP}{\lab{\otimes}}
\newcommand{\compA}{\lab{\oast}}
\newcommand{\compJ}{\lab{\varovee}}
\newcommand{\compB}{\lab{\varogreaterthan}}

\newcommand{\Vect}[2]{\VectOp\ #1\ #2}

\newcommand{\Path}{\lightning}

\newcommand{\StoreSym}{\Mapsto}
\newcommand{\StoreNP}[2]{\ensuremath{#1 \StoreSym #2}}
\newcommand{\Store}[2]{(\StoreNP{#1}{#2})}

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

% \specialcomment{todoP}{\begingroup\color{red}TODO: }{\endgroup}

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
\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\scw}[1]{\authornote{magenta}{SCW}{#1}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}
\newcommand{\etal}{\emph{et al.}\xspace}

\newcommand{\term}[1]{\emph{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\def\titlerunning{Labelled structures and combinatorial species}

\title{\titlerunning}

%% SIGPLAN
% \authorinfo{Brent A. Yorgey \\ Stephanie Weirich}
% {Dept. of Computer and Information Science\\ The University of Pennsylvania\\
% Philadelphia, Pennsylvania, USA}
% {\{byorgey,sweirich\}@@cis.upenn.edu}

% \authorinfo{Jacques Carette}
% {Dept. of Computing and Software\\ McMaster University\\
% Hamilton, Ontario, Canada}
% {carette@@mcmaster.ca}

%% LNCS
% \author{Brent A. Yorgey\inst{1} \and Jacques Carette\inst{2} \and Stephanie Weirich\inst{1}}
% \institute{Dept. of Computer and Information Science\\
% The University of Pennsylvania\\
% Philadelphia, Pennsylvania, USA
% \and
% Dept. of Computing and Software\\ McMaster University\\
% Hamilton, Ontario, Canada}

%% EPTCS
\author{
  Brent A. Yorgey \quad\quad Stephanie Weirich
  \institute{
    Dept. of Computer and Information Science\\
    The University of Pennsylvania\\
    Philadelphia, Pennsylvania, USA
  }
  \and
  Jacques Carette
  \institute{
    Dept. of Computing and Software\\ McMaster University\\
    Hamilton, Ontario, Canada
  }
}

\def\authorrunning{B. Yorgey, J. Carette, S. Weirich}

\begin{document}

\maketitle

\begin{abstract}

  We describe a theory of \term{labelled structures}, which
  intuitively consist of a labelled shape together with a mapping from
  labels to data. Labelled structures thus subsume algebraic data
  types as well as ``labelled'' types such as arrays and finite maps.
  The idea of decomposing container structures into shapes and data is
  an old one. The novel idea is to explicitly mediate the
  decomposition with arbitrary labels, and we demonstrate benefits of
  this approach in implementing and reasoning about operations
  naturally expressed as operations on labels, explicitly modelling
  value-level sharing, and reasoning about memory allocation and
  layout.

  The theory of labelled structures is built directly on the
  foundation of \emph{combinatorial species}, which serve to describe
  labelled shapes.  The theory of species bears striking similarities
  to the theory of algebraic data types, and it has long been
  suspected that a more precise and fruitful connection could be made
  between the two.  In a larger sense, the aim of this paper is to
  serve as a first step in connecting combinatorial species to the
  theory and practice of programming.  In particular, we describe a
  ``port'' of the theory of species into constructive type theory,
  justifying its use as a basis for computation.

\end{abstract}

% \category{D.3.2}{Programming Languages}{Applicative (functional) languages}

% \terms
% Languages, Types


\scw{I've been thinking about the structure of this paper, trying to make it
tell its story more effectively.
The focus of the paper should be on labelled structures. The fact that they
are directly inspired by combinatorial species is great and should be
mentioned repeatedly, but in the end, it is not what the paper is about.
Our introduction mostly works with this format, but we could bring it out.
I'm imagining a progression like:
\begin{itemize}
\item What is a labelled structure? A decomposition of data structure. More
formally, a labelled shape combined with a mapping from labels to data values.
\item What is novel about this definition?
\begin{itemize}
  \item Labels must be drawn from some finite set, but can have their own
  structure
  \item We define the mapping from labels to data values abstractly. It
    doesn't need to be injective.
\end{itemize}
\item What is important about our definition?
\begin{itemize}
  \item Non-injective mappings represent sharing in data structures, something
    that is unobservable for algebraic datatypes.
  \item Although labels have structure, we make it convenient to work up to (partial)
    isomorphism. ``Relabeling'' models certain operations on data, sometimes
    more efficiently that with more standard representations.
  \item We can choose a definition of mapping that lets us reason about memory
    allocation and layout.
\end{itemize}
\end{itemize}
However, once we are past the introduction, the story gets muddled. Part of
this may be that I'm more of a fan of a top-down presentation, whereas the
current state is more bottom-up. Perhaps we could use more concrete examples
of what we are trying to do in Section 2 (although explaining them informally)
before diving into the mathematical preliminaries. Section 3 is called
``Cominatorial Species'', though perhaps we should call it ``Labelled
shapes''. I'm not sure how important it is to start with the set-theoretic
definition first. Why not start with the real definition, and then later
explain why it is different in type theory than in set theory?  Are there
interesting examples of labelled shapes we can give at the end of section 3?
Or remarks to make about labels?  Section 4 dives into mappings. We present
mappings as one thing, but then change it to something else in 4.3. Why not
just start with the definition that we want in the first place?  Section 5
seems a little strange to me because it starts talking about eliminators
before talking about where we get labelled structures in the first place
(Section 6). And section 6 mixes the construction of labelled shapes with the
construction of labelled structures. Maybe it makes sense to combine these
explanations, but we need to be more explicit about what we are doing. Sec 6
also doesn't really connect to the finite map/array examples mentioned
before. Can we show an example of constructing an array?  }

\jc{Right.  The more we worked on this, the more the picture evolved, and
I think Stephanie's comments really illustrates our current state best.  I
would be quite happy with the paper layout that she suggests.  Although
there is one item which needs serious re-thinking: the emphasis on 'finite'.
As things currently stand, our use of 'finite' keeps getting smaller and
smaller.  In a number of places, I think we could weaken the definition
of finiteness too (from an isomorphism to simply requiring a surjection 
from some bounded set of naturals onto our labels, with no injectivity
requirement; in other places we need an (unordered) enumeration instead).}
\jc{Regarding array examples: we do not have any code on arrays that works
at the moment.  We do have code for 1D sized vectors that mostly works.
We have all sorts of other examples that also work.  We should really agree 
on which examples we'll pull from, and make sure they fully work.}

\section{Introduction}
\label{sec:intro}

The theory of combinatorial species \citation{joyal,bll}, as it relates to the
theory and practice of programming languages, has long seemed to the authors
``an answer looking for a question'': the theory is too beautiful, and too
``obviously'' related to algebraic data types, to have no applications
whatsoever.  Teasing out the precise relationship between species and
data types, however, has proved challenging, for two reasons. First,
combinatorialists are mainly concerned with enumerating and
generating abstract structures, not with storing and computing with data.
Thus, in order to apply species in a computational setting,
there are many hidden assumptions and glossed distinctions that must
first be made explicit.  Second, being situated in traditional mathematical
practice rooted in set theory, species are usually described in ways
that are \emph{untyped} and \emph{nonconstructive}, both of which
hinder adoption and understanding in a computational context.

\todo{sprinkle some forward references to the rest of the paper
  through the following}

From a computational point of view, the right way to think about
species is as \emph{labelled shapes} which do not contain any data.
To recover a notion of \emph{data} structures, one must add a (notion
of) mapping from labels to data.  This leads to the familiar idea of
decomposing data structures as shapes plus data
\citep{abbott_categories_2003, jay-shapely}, with labels mediating
between the two.  Informally, this pairing of a labelled shape
(corresponding to a species) and a mapping from labels to data values
is what we call a \term{labelled structure}\footnote{Following
Flajolet et al's lead \citation{FlSaZi91,FlajoletZC94}.}.
For example,
\pref{fig:labelled-structure-example} illustrates a labelled tree
shape paired with a mapping from labels to data.  A \emph{family} of
labelled structures refers to a class of structures parameterized over
the label type $L$ and (typically) the data type $A$.

\begin{figure}
  \centering
\begin{diagram}[width=300]
import Graphics.SVGFonts.ReadFont
import Diagrams.Points
import Data.Tree
import Diagrams.TwoD.Layout.Tree
import SpeciesDiagrams

mkL n = (aLabels !! n) # scale 0.5 # fc black <> circle 0.7 # fc white

t = Node 2 [Node 1 [], Node 4 [Node 3 [], Node 0 [], Node 5 []]]

d = renderTree mkL (~~) (symmLayout' with { slHSep = 3.5, slVSep = 3.5 } t)

mapping = centerX . hcat $ zipWith mkMapping [0..5] "SNAILS" -- $
  where
    mkMapping i c = mkL i ==== (text' 1.5 [c] <> square 2)

dia = (d # centerY ... strutX 4 ... mapping)
    # centerXY # pad 1.1

infixl 6 ...
infixl 6 ====
(...) = (||||||)
x ==== y = x === strutY 0.5 === y
\end{diagram}
  \caption{A labelled structure with six labels}
  \label{fig:labelled-structure-example}
\end{figure}

Note that the mapping from labels to data values need not be
injective, so the same value of type $A$ may be associated to multiple
labels, as illustrated in \pref{fig:labelled-structure-example}.
However, the mapping must of course be functional, that is, each label
is assigned to exactly one value.

For now, we leave the notion of ``labelled shape'' abstract; we will
return to define it more precisely in \pref{sec:species}.  Instead, we
turn to a collection of examples showing the possibilities afforded by
this framework.

\paragraph{Algebraic data types}

All the usual algebraic data types have corresponding families of
labelled structures, where values of the algebraic data type are used
as labelled shapes.  Given such a labelled structure we can
``collapse'' it back to an algebraic data structure by substituting
data for labels.  For example, the labelled tree structure in
\pref{fig:labelled-structure-example} represents the tree containing
\texttt{A} at its root, \texttt{N} as the left child, and so on.  Note
that the family of labelled tree structures is quite a bit larger than
the usual tree type: every possible labelling of a given tree shape
results in a different labelled structure, whereas there are many
labelled tree structures that will ``collapse'' to the same algebraic
data structure, which differ only in the way they are labelled.

\jc{Give a forward reference to how we can associate canonical labels
to algebraic data types?}

\jc{Comment to be moved to the right place, but it came to mind while I
was reading the above: this `late' collapse joins up nicely with HTT 
and higher-categorical thinking.  In this style, rather than quotienting
early (to find an efficient representation eagerly), it is thought best
to wait and record the collapse through adjoining an groupoid of 
isomorphisms [think identity types].  The `best' picture may then 
emerge much later from a \emph{composition} of isomorphisms, rather than
directly from the first isomorphism encountered.}

\paragraph{Finite maps}

Since the definition of a labelled structure already includes the
notion of a mapping from labels to data, we may encode finite maps
simply by using \emph{sets} of labels as shapes, \ie\ shapes with no
structure other than containing some labels. Furthermore, we can
directly model multiple finite map implementations (\todo{see section
  ???}).

\paragraph{Vectors and arrays}

\jc{As I said above, I am uncomfortable with saying too much about
multi-dimensional arrays until our implementation catches up.  I think 
what I'll do is finish this read through/edit pass, then work on the array
ideas, so that we can keep this example family in place.}

Vectors, and multi-dimensional arrays more generally, can be modeled as
finite maps with nontrivial structure on their labels---for example,
2D arrays have labels from a product type.  Real-world
programs that deal with arrays often care about the precise way in
which the arrays are allocated and laid out in memory; we can directly
model this (\todo{section ???}).

\paragraph{Value-level sharing}

Structures with shared labels can be used to model (value-level)
\emph{sharing}.  For example, we can superimpose both a binary tree
and a list structure on some data, as shown in
\pref{fig:tree-list-share}.

\begin{figure}
  \centering
  \begin{diagram}[width=200]
import           Data.List.Split
import           Diagrams.TwoD.Layout.Tree
import           Diagrams.TwoD.Path.Metafont

import           SpeciesDiagrams

leaf1 = circle 1 # fc white # named "l1"
leaf2 = circle 1 # fc white # named "l2"

tree = maybe mempty (renderTree (const leaf1) (~~))
     . symmLayoutBin' with { slVSep = 4, slHSep = 6 }
     $ (BNode () (BNode () (BNode () Empty (BNode () Empty Empty)) Empty) (BNode () (BNode () Empty Empty) (BNode () Empty Empty)))

listL shp l = hcat . replicate 7 $ (shp # fc white # named l)

connectAll l1 l2 perm =
  withNameAll l1 $ \l1s ->
  withNameAll l2 $ \l2s ->
  applyAll (zipWith conn l1s (perm l2s))

conn l1 l2 = beneath (lc grey . metafont $ location l1 .- leaving unit_Y <> arriving unit_Y -. endpt (location l2))

dia = vcat' (with & sep .~ 5)
  [ hcat' (with & sep .~ 5)
    [ tree # centerY
    , listL (circle 1) "l2" # centerY
    ] # centerXY
  , listL (square 2) "s" # centerXY
  ]
  # connectAll "l1" "s" id
  # connectAll "l2" "s" (concat . map reverse . chunksOf 2)
  # centerXY # pad 1.1
  \end{diagram} %$
  \caption{Superimposing a tree and a list on shared data}
  \label{fig:tree-list-share}
\end{figure}

Though this bears many similarities to previous approaches, there is
one key difference: whereas previous approaches have used a fixed,
\jc{citations to previous approaches?}
canonical set of labels (or left the labels entirely implicit),
species naturally lead one to work
\emph{parametrically}\scw{???}\bay{What do you find confusing about this?} over labels,
giving the labels a much more prominent role.  Bringing the mediating
labels to the fore in this way is, to our knowledge, novel, and leads
to some interesting benefits.  For example:
\begin{itemize}
\item It allows us to unify ``implicitly labelled'' structures (such as
  algebraic data types) and ``explicitly labelled'' structures (such as
  vectors and finite maps) under the same framework.
\item Some operations (for example, reversing a vector, taking the
  transpose of a 2D array, or altering the keys of a finite map) can
  be more naturally described as \emph{operations on labels}, leading
  to benefits in both reasoning and efficiency (see \todo{section ?}).
  \scw{Are we sure that it is more efficient? What about the copying that
    may need to be done to adjust the labels/maps?}\jc{It should be more
    efficient for large data think local index and distributed data --
    there was an ICFP talk about exactly this.}
\item Value-level \emph{sharing} can be easily modelled via shared
  labels (see \todo{section?})---in contrast, this is not possible if
  every structure has a fixed set of canonical labels.
\item In fact, labels share some of the properties of memory
  addresses, \ie\ pointers, and taking this analogy seriously lets us
  reason about memory allocation and layout for stored data
  structures (see \todo{section?}).
\item It opens the possibility of taking labels and relabellings from
  a category other than $\B$ (as is done, for example, with
  $\mathbb{L}$-species \cite{Joyal86}, \cite[chapter 5]{bll}).  We conjecture 
  that this has also benefits in a computational setting, though exploring
  this idea in more detail is left to future work.
\end{itemize}

\jc{The paragraph below goes in a different direction, but in the text
it reads as if it were a continuation of value-level sharing.  We should
visually indicate this break - maybe via subsections?}
It is important to remember that species are defined over \emph{finite}
sets of labels.  In a classical setting, while finiteness is a crucial part of
the definition, it is otherwise a fairly implicit feature of the actual
theory.  Combinatorialists do not need to remind themselves of this 
finiteness condition, as it is a pervasive axiom that you can only ``count''
finite collections of objects.  When ported to a 
constructive setting, however, the notion
of finiteness takes on nontrivial computational content and
significance.  In particular, we are naturally led to work up to
computationally relevant \emph{equivalences} (and \emph{partial
  equivalences}) on labels.  Working up to equivalence in this way
confers additional expressive power, allowing us to model efficient
label operations (\eg partition) without copying.  In fact,
this is one of the key ingredients in modeling memory layout and
allocation (see \todo{section?}).

In more detail, our contributions are as follows:
\begin{itemize}
\item We describe a ``port'' of combinatorial species from set theory
  to constructive type theory, making the theory more directly
  applicable in a programming context, more accessible to functional
  programmers, and incidentally illuminating some new features of the
  theory.
\item We define a generic framework for \term{labelled types} on top
  of this basis, showing how to include them in practical
  programming languages.
\item We show how to accomplish \emph{memory defragmentation} using
  constructive subset evidence and the \emph{Gordon complementary
    bijection principle} (\todo{ref}).
\item We describe some novel introduction forms for structures built
  as the composition of other structures (\pref{sec:species-ops}).
\item We give extended examples showing the utility of labelled types,
  including \todo{?}
\end{itemize}

It is worth mentioning that in previous work
\citep{carette_species, yorgey-2010-species} we
conjectured that the benefits of the theory of species would lie
primarily in its ability to describe data types with \term{symmetry}
(\ie\ quotient types \cite{quotient-types}).  That promise has not
gone away; but we were amused to discover that a functor category
would seem to shed its brightest light on low-level issues like memory
allocation, layout and sharing.

\section{Theoretical setting}
\label{sec:prelim}

We have found it quite convenient to work within (a small fragment of)
\emph{homotopy type theory} (HoTT)~\cite{hott}.  We do not actually need much
complex machinery from the theory, and simply summarize the most important
ideas and notation here.  Everything in this paper could be formalized
in most any standard constructive type theory; we choose to work in
HoTT because of its emphasis on equality and isomorphism, which plays
a large role.  In fact, it seems likely that there are deeper
connections between homotopy type theory and the theory of species,
but exploring these connections is left to future work.

The concept of \term{finiteness} plays a central (but implicit) r\^{o}le in 
the theory of combinatorial species, primarily through the pervasive use
of generating functions.  While its r\^{o}le is not as central in our
setting, it is important enough to give the precise definition we use,
seeing as there are multiple constructive interpretations of finiteness.

\subsection{A fragment of homotopy type theory}
\label{sec:HoTT}

The type theory we work with is equipped with an empty type \TyZero, a unit
type \TyOne (with inhabitant $\unit$), coproducts (with constructors $\inl$
and $\inr$), dependent pairs (with projections $\outl$ and $\outr$),
dependent functions, a hierarchy of type universes $\Type_0$,
$\Type_1$, $\Type_2$\dots (we usually omit the subscripts), and a
notion of propositional equality.  Instead of writing the traditional
$\sum_{x : A} B(x)$ for the type of dependent pairs and $\prod_{x:A}
B(x)$ for dependent functions, we will often use the Agda-like
\cite{Agda} notations $(x:A) \times B(x)$ and $(x:A) \to B(x)$,
respectively (though we still occasionally use $\Sigma$ and $\Pi$ for
emphasis).  We continue to use the standard abbreviations $A \times B$
and $A \to B$ for non-dependent pair and function types, that is, when
$x$ does not appear free in $B$. Also, to reduce clutter, we sometimes
make use of implicit quantification: free type variables in a
type---like $A$ and $B$ in $A \times (B \to \N)$---are implicitly
universally quantified, like $(A : \Type) \to (B : \Type) \to A \times
(B \to \N)$.

We use $\N : \Type$ to denote the usual inductively defined type of
natural numbers, with constructors $\NatZ : \N$ and $\NatS : \N \to
\N$.  We also make use of the usual indexed type of canonical finite
sets $\Fin : \N \to \Type$, with constructors $\FinZ : \impl{n :
\N} \to \Fin (\NatS n)$ and $\FinS : \impl {n : \N} \to \Fin n \to \Fin
(\NatS n)$.

$A \iso B$ is the type of \term{equivalences} between $A$ and $B$
(intuitively, pairs of inverse functions $f : A \to B$ and $g : B \to
A$).\footnote{The precise details are more subtle \cite[Chapter
  4]{hott}, but unimportant for our purposes.}  We overload the
notations $\id$ and $\comp$ to denote the identity equivalence and
equivalence composition respectively; we also allow equivalences of
type $A \iso B$ to be implicitly used as functions $A \to B$ where it
does not cause confusion.  We use the notation $\mkIso$ for
constructing equivalences from a pair of functions. That is, if $f : A
\to B$ and $g : B \to A$ are inverse, then $f \mkIso g : A \iso B$;
the proof that $f$ and $g$ are inverse is left implicit.  For $T :
\Type \to \Type$ and $\sigma : A \iso B$ we can also construct the
equivalence $T\ \sigma : T\ A \iso T\ B$.\footnote{Formally, this is
  justified by the univalence axiom and the guaranteed functoriality
  of $T$.} For example, $\sigma \times (\sigma \to C) : A \times (A
\to C) \iso B \times (B \to C)$, given by \[ \sigma \times (\sigma \to
C) = (\lam{(a,f)}{(\sigma\ a, f \comp \sigma^{-1})} \mkIso
(\lam{(b,g)}{(\sigma^{-1}\ b, f \comp \sigma)}) \]

\noindent For our purposes, this is sufficient:  in other words,
equivalences between labels are informative, but equivalences between
equivalences yield no further useful information.

\subsection{Finiteness}
\label{sec:finiteness}

There are many possible constructive interpretations of
finiteness \todo{make a citation:
  \url{http://ncatlab.org/nlab/show/finite+set}}; the one we need is
the simplest: a finite set is one which is in bijection to a canonical
set of a known size. That is,
\[ \Finite A \defn (n : \N) \times (\Fin n \iso A). \]

It is tempting to use mechanisms for implicit evidence, such as
Haskell's \emph{type class} mechanism, to record the finiteness of
types.  That is, we could imagine defining a type class
\begin{spec}
class IsFinite a where
  isFinite :: Finite a
\end{spec}
The idea is that the statement ``the type $A$ is finite'' translates
to ``$A$ is an instance of the |IsFinite| class''.  However, this is
not what we want.  The bare statement ``the type $A$ is finite''
intuitively corresponds to the \emph{propositional truncation}
$\||\Finite A\||$, that is, the knowledge simply that $\Finite A$ is
inhabited, without knowing anything specific about the inhabitant.
This is a rather different beast than a type class instance
$|IsFinite|\ A$, which corresponds to a \emph{canonical choice} of an
inhabitant of $\Finite A$.  Inhabitants of $\Finite A$, however, have
nontrivial computational content; it really matters \emph{which}
inhabitant we have.  Thus, instead of simply passing around types and
requiring them to have an implicit, canonical finiteness proof, we
will in general pass around types \emph{together with} some specific
finiteness proof.  We can encapsulate this by defining \[ \FinType
\defn (L : \Type) \times \Finite L \] as the universe of finite types.

It is not hard to see that the size of a finite type is determined
uniquely. That is, if $f_1, f_2 : \Finite L$ are any two witnesses that
$L$ is finite, then $\outl(f_1) = \outl(f_2)$.  (As proof, note that if
$f_1 = (n_1, i_1)$ and $f_2 = (n_2, i_2)$, then $i_2^{-1} \comp i_1 :
\Fin{n_1} \iso \Fin{n_2}$, from which we can derive $n_1 = n_2$ by
double induction.) In a slight abuse of notation, we write
$\size{L}$ to denote this size.  Computationally, this corresponds to
applying $\outl$ to some finiteness proof; but since it does not
matter which proof we use, we simply leave it implicit, being careful
to only use $\size -$ in a context where a suitable finiteness proof
can be obtained.

\section{Combinatorial Species}
\label{sec:species}

% We want to think of each labelled structure as \emph{indexed by} its
% set of labels (or, more generally, by the \emph{size} of the set of
% labels).  We can accomplish this by a mapping from label sets to all
% the structures built from them, with some extra properties to
% guarantee that we really do get the same family of structures no
% matter what set of labels we happen to choose.

Our theory of labelled structures is inspired by, and directly based
upon, the theory of \term{combinatorial species} \cite{joyal}.  We
give a brief introduction to it here; the reader interested in a
fuller treatment should consult \citet{bll}.  Functional programmers
may wish to start with~\cite{yorgey-2010-species}.

\subsection{Species, set-theoretically}
\label{sec:set-species}

We begin with a standard set-theoretic definition of species
(essentially what one finds in \citet{bll}, but with slightly
different terminology).  We will upgrade to a \emph{type}-theoretic
definition in \pref{sec:constructive-species}, but it is worth seeing
both definitions and the relationship between them.

\begin{definition}
A \term{species} is a pair of mappings, both called $F$, that
\begin{itemize}
\item sends any finite set $L$ (of \term{labels}) to a finite set
  $F(L)$ (of \term{shapes}), and
\item sends any bijection on finite sets $\sigma : L \leftrightarrow L'$ (a
  \term{relabelling}) to a function $F(\sigma) : F(L) \to F(L')$,
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
(when $L$ is clear from context) just ``$F$-shapes''.  $F(\sigma)$
is called the ``transport of $\sigma$ along $F$'', or sometimes the
``relabelling of $F$-shapes by $\sigma$''.

In the existing literature, elements of $F(L)$ are usually called
``$F$-structures'' rather than ``$F$-shapes''.  To a combinatorialist,
labelled shapes are themselves the primary objects of interest;
however, in a computational context, we must be careful to distinguish
between labelled \emph{structures} (which, in our terminology, have
data associated with the labels) and bare labelled \emph{shapes}
(which do not).

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

As before, a species is a pair of maps, one mapping label types to
sets of shapes, and one relabelling shapes. However, the $\Species$ type
also requires proofs of the functoriality conditions for the
relabeling function.
\begin{align*}
\Species & \defn (\shapes : \FinType \to \Type) \\
         & \times (\relabel : (L_1, L_2 : \FinType) \to (L_1 \iso L_2) \to
           (\shapes\ L_1 \to \shapes\ L_2)) \\
         & \times ((L : \FinType) \to \relabel \id_L = \id_{\shapes L}) \\
         & \times ((L_1, L_2, L_3 : \FinType) \to (\sigma : L_2 \iso
         L_3) \\ &\qquad\to (\tau : L_1 \iso L_2) \to
(\relabel\ (\sigma \comp \tau) = \relabel \sigma \comp \relabel \tau))
\end{align*}

Where the meaning is clear from context, we will use simple
application to denote the action of a species on both label types and
relabellings. That is, if $F : \Species$, $L, L' : \FinType$, and $\sigma
: L \iso L'$, we will just write $F\ L : \Type$ or $F\ \sigma : F\
L \to F\ L'$ without explicitly projecting out the $\shapes$ and
$\relabel$ functions.

In \pref{sec:set-species}, the codomain of species was defined as the
category of \emph{finite} sets, but in the above definition the
codomain of $\shapes$ is $\Type$ rather than $\FinType$.
Constructively, the finiteness of the codomain does not seem very
important---all the basic definitions and constructions work
unchanged.  One place where the finiteness of the codomain comes into
play is in setting up homomorphisms from species to generating
functions with coefficients taken from $\N$---though we conjecture
that taking coefficients from the ring over the one-point
compactification of the naturals, $\N \cup \{\infty\}$, works just as
well.  There may be some theorems (\eg molecular species
decomposition, or the implicit species theorem) which only hold with a
finite codomain---in the future, we plan to port some standard
theorems about species to a constructive setting to see where the
finiteness is required.

It is interesting to note that an equivalence $L_1 \iso L_2$ between
constructively finite types $L_1,L_2 : \FinType$, as required by
$\relabel$, contains more than first meets the eye.  Since \[ \FinType
\defn (L : \Type) \times \Finite L \equiv (L : \Type) \times (n : \N)
\times (\Fin n \iso L), \] such equivalences contain not just an
equivalence between the underlying types, but also an
equivalence-between-equivalences requiring them to be finite ``in the
same way'', that is, to yield the same equivalence with $\Fin n$ after
mapping from one to the other.  The situation can be pictured as shown
in \pref{fig:fin-equiv}, where the diagram necessarily contains only
triangles: corresponding elements of $L_1$ and $L_2$ on the sides
correspond to the same element of $\Fin n$ on the bottom row.
\begin{figure}
  \centering
  \begin{diagram}[width=150]
import           Data.Bits                      (xor)
import           SpeciesDiagrams

mkList n d f = hcat' (with & sep .~ 2 & catMethod .~ Distrib)
  (zipWith named (map f [0::Int ..]) (replicate n d))

n :: Int
n = 8

dia = decorateLocatedTrail (triangle (fromIntegral (n+2)) # rotateBy (1/2))
      [ "l1"  ||> (l1 # rotateBy (-1/3))
      , "fin" ||> fin
      , "l2"  ||> (l2 # rotateBy (1/3))
      ]
      # mkConnections
      # centerXY # pad 1.2
      # flip appends
        [ (unit_Y                  , text' 4 "Fin n")
        , (unit_Y # rotateBy (-1/3), text' 4 "L₁"   )
        , (unit_Y # rotateBy (1/3) , text' 4 "L₂"   )
        ]
  where
    fin = mkList n dot (`xor` 1) # centerXY
    l1  = mkList n dot id # centerXY
    l2  = mkList n dot ((n-1) -) # centerXY
    dot = circle 0.5 # fc grey
    mkConnections = applyAll
      [  withNames [a .> i, b .> i] $ \[p,q] -> atop (location p ~~ location q)
      || (a,b) <- take 3 . (zip <*> tail) . cycle $ ["l1", "fin", "l2"]
      ,  i <- [0 .. (n-1)]
      ]
  \end{diagram}
  \caption{An equivalence between constructively finite types contains
  only triangles}
  \label{fig:fin-equiv}
\end{figure}
Intuitively, this means that if $L_1, L_2 : \FinType$, an equivalence
$L_1 \iso L_2$ cannot contain ``too much'' information: it only tells
us how the underlying types of $L_1$ and $L_2$ relate, preserving the
fact that they can both be put in correspondence with $\Fin n$ for
some $n$.  In particular, it cannot encode a nontrivial permutation on
$\Fin n$.

\section{Mappings}
\label{sec:mappings}

\todo{high-level explanation}

\subsection{Mappings, take I}
\label{sec:storage}

Our goal is to define a labelled structure as a labelled shape paired
with a \emph{mapping} from labels to data.  What, precisely, do we
mean by a \emph{mapping}?  In fact, we need not pin down a particular
implementation.  We require only that implementations of $\Store - - : \FinType
\to \Type \to \Type$ come equipped with the following operations:
\begin{align*}
  |allocate| &: (L \to A) \to \Store L A \\
  |index|  &: \Store L A \to L \to A \\
  |append| &: \Store {L_1} A \to \Store {L_2} A \to \Store {(L_1 + L_2)} A \\
  |concat| &: \Store {L_1} {\Store {L_2} A} \to \Store {(L_1 \times
    L_2)} A \\
  |map| &: (A \to B) \to \Store L A \to \Store L B \\
  |zipWith| &: (A \to B \to C) \to \Store L A \to \Store L B \to \Store L C \\
  |reindex|  &: (L' \iso L) \to \Store L A \to \Store {L'} A
\end{align*}
One could also imagine requiring similar operations like $|replace| :
L \to A \to \Store L A \to A \times \Store L A$, but these are the
operations we need in the context of this paper. The semantics of
these operations can be specified by various laws (for example,
|allocate| and |index| are inverse; |index| and |reindex| commute
appropriately with the other operations; and so on). For now, we will
content ourselves with some informal descriptions of the semantics.

\bay{The interesting thing that needs to be worked out here is what
  type formers mean when ``lifted'' to $\FinType$ (and whether it even
  makes sense to lift them thus).  \eg if $L_1,L_2 : \FinType$, then
  what is $L_1 + L_2$?  Note, presumably it has to include a proof $\outr(L_1) +
  \outr(L_2) \iso \Fin(|L_1| + |L_2|)$, which encodes a canonical
  choice of how to do the summing.}

\begin{itemize}
\item First, |allocate| is the sole means of constructing $\Store L A$
  values, taking a function $L \to A$ as a specification of the
  mapping. Note that since $L : \FinType$, implementations of
  |allocate| also have access to a constructive proof that $L$ is
  finite.  Intuitively, this is necessary because allocation may
  require some intensional knowledge about the type $L$.  For example,
  as explained below, we may implement $\Store L A$ using a vector of
  $A$ values; allocating such a vector requires knowing the size of
  $L$.
\item |index| allows looking up data by label.
\item |append| and |concat| are ``structural'' operations, allowing us
  to combine two mappings into one, or collapse nested mappings,
  respectively.
\item |map| ensures that $\Store L -$ is functorial.
\item |zipWith| gives us a way to combine the contents of two mappings
  labelwise.
\item $|reindex| : (L' \iso L) \to \Store L A \to \Store {L'} A$
  expresses the functoriality of $\Store - A$: we can change from one
  type of labels to another by specifying an equivalence between them.
\end{itemize}
 \todo{is it worth actually
  formulating/spelling out the laws?  are any of them particularly
  interesting? are there any interesting choices to be made?}

We can give a particularly simple implementation using a function
arrow to represent $\StoreSym$ (presented here using Haskell-like
notation):

\begin{spec}
  allocate         = id
  index            = id
  append f g       = either f g
  concat           = curry
  map              = (.)
  zipWith z f g    = \l -> z (f l) (g l)
  reindex i f      = f . i
\end{spec}

Note that the implementation of |allocate| does not take into account
the finiteness of $L$ at all, and the implementation of |reindex| uses
a slight abuse of notation to treat $s : L' \iso L$ as a function $L'
\to L$.

A more interesting implementation uses finite vectors to store the $A$
values.  In particular, we assume a type $|Vec| : \N \to \Type \to
\Type$ of length-indexed vectors, supporting operations
\begin{align*}
  |allocateV| &: (n : \N) \to (\Fin n \to A) \to \Vect n A \\
  |(!)|       &: \Vect n A \to \Fin n \to A \\
  |mapV|      &: (A \to B) \to (\Vect n A \to \Vect n B) \\
  |foldV|     &: R \to (R \to A \to R) \to \Vect n A \to R \\
  |appendV|   &: \Vect m A \to \Vect n A \to \Vect {(m + n)} A \times
  (\Fin m + \Fin n \iso \Fin{(m + n)}) \\
  |concatV|   &: \Vect m {(\Vect n A)} \to \Vect {(m \cdot n)} A \times
  (\Fin m \times \Fin n \iso \Fin (m \cdot n))\\
  |sumV|      &: (|ns| : \Vect m \N) \to |mapV (\n -> Vec n A) ns| \\
  &\qquad \to \Vect {(|sumN ns|)} A \times
  (|sumTy|\ (|mapV|\ \Fin{}\ |ns|) \iso \Fin (|sumN ns|))
%  imapV     &: (\Fin n \to A \to B) \to (\Vect n A \to \Vect n B) \\
%  zipWithV  &: (A \to B \to C) \to \Vect n A \to \Vect n B \to \Vect n C
\end{align*}
Note that in addition to computing new vectors, |appendV| and
|concatV| also yield isomorphisms which encode the precise
relationship bewteen the indices of the input and output vectors.  For
example, if |appendV v1 v2 = (v,e)|, then it must be the case that |v1
! m = v !  (e (inl m))|.  Similarly, |v ! m ! n = v' ! (e (m,n))| when
|concatV v = (v',e)|. |sumV| is a generalized version of |concatV|
allowing the concatenation of a collection of vectors of varying
length,
\begin{equation*}
  \begin{minipage}[c]{200pt}
  \hfill
  \begin{diagram}[height=15]
    dia = pad 1.1 . centerXY
        . hcat' (with & sep .~ 0.5) . map (hcat . flip replicate (square 1))
        $ [ 4, 2, 5 ]
  \end{diagram}
  %$
  \end{minipage}
  \stackrel{|sumV|}{\longrightarrow}
  \begin{minipage}[c]{200pt}
  \begin{diagram}[height=15]
    dia = pad 1.1 . centerXY
        . hcat . flip replicate (square 1) . sum
        $ [ 4, 2, 5 ]
  \end{diagram}
  %$
  \end{minipage}
\end{equation*}
with |sumN = foldV 0 (+)| and |sumTy = foldV undefined (+)|.

Given such a type $\cons{Vec}$, we may define \[ \Store L A \defn \sum_{n :
  \N} (L \iso \Fin n) \times \Vect n A, \] and implement the required
operations as follows:

\begin{itemize}
\item The implementation of |allocate| uses the provided $\Finite L$
  proof to determine the size of the vector to be allocated, as well
  as the initial layout of the values.
  \begin{spec}
    allocate fin@(n, iso) f = (n, fin, allocateV n (f . iso))
  \end{spec}

\item To reindex, there is no need to allocate a new vector; |reindex|
  simply composes the given equivalence with the stored one.
  \begin{spec}
    reindex i' (n, i, v) = (n, i . i', v)
  \end{spec}

\item |index| is implemented in terms of |(!)|, using the stored
  equivalence to convert an external label $L$ into an internal index
  of type $\Fin n$.

\item |map| is implemented straightforwardly in terms of |mapV|; since
  the type $L$ and the length of the underlying vector are not
  affected, the proof $(L \iso \Fin n)$ can be carried through
  unchanged.

\item At first blush it may seem that |zipWith| would be equally
  straightforward to implement in terms of a function $|zipWithV| : (A
  \to B \to C) \to \Vect n A \to \Vect n B \to \Vect n C$ (if we had
  such a function).  The problem, however, is that the $(L \iso \Fin
  n)$ proofs have real computational content: zipping on labels may
  not coincide with zipping on indices. \todo{need some pictures to
    make this more clear?} Since we want to zip on indices, |zipWith|
  must compose the given equivalences to obtain the correspondence
  between the label mappings used by the two input vectors:
  \begin{spec}
    zipWith f (n, i1, v1) (_, i2, v2) = (n, i2, v)
      where v = allocateV n (\k -> f (v1 ! (i1 . inv(i2)) k) (v2 ! k))
  \end{spec}
  Note that the output of |zipWith f s1 s2| reuses the label
  equivalence |i2| from |s2|.  Of course we could instead have chosen
  to reuse |i1| instead, but these are the only possible choices.
  Given the choice of |i2|,  an optimizing compiler can compile |zipWith|
  into in-place update on |s2| when it can prove that the old value
  is no longer needed.

\item |append| is straightforward to implement via |appendV|:
  \begin{spec}
    append (n1, i1, v1) (n2, i2, v2) = (n1+n2, e . (i1 + i2), v)
      where (v,e) = appendV v1 v2
  \end{spec}
  Note that we construct the required label equivalence as the
  composite \[ L_1 + L_2 \stackrel{i_1 + i_2}{\iso} \Fin{n_1} +
  \Fin{n_2} \stackrel{e}{\iso} \Fin{(n_1 + n_2)}, \] using the index
  equivalence |e| returned by |appendV|.

\item |concat| is implemented similarly to |append|: we multiply the
  sizes, use |concatV| on the input vector-of-vectors, and compute the
  right equivalence by \todo{urgh, actually we have to sum over them,
    not just take a product, because there may be \emph{many}
    equivalences $L_2 \iso \Fin{n_2}$, one for each inner vector.}

\end{itemize}

In this instance, the labels are acting like (generalized)
``pointers'', and the label equivalences yield some built-in ``pointer
indirection'', allowing us to manipulate the labels without incurring
a lot of (potentially expensive) allocation and copying. Data
structures ultimately have to be stored in memory somehow, and this
gives us a nice ``end-to-end'' theory that is able to model
both high-level concerns as well as low-level operational details.

Note that when |appendV| and |concatV| cannot be optimized to in-place
updates, they must allocate an entire new vector in memory.  To avoid
this in exchange for some bookkeeping overhead, we could make a deep
embedding out of the vector operations, turning |appendV| and
|concatV| (and possibly |allocateV| and |mapV| as well) into
\emph{constructors} in a new data type.  This results in something
that looks very much like generalized tries
\cite{Hinze-generalized-tries}.

\todo{Motivate partial isos, subset relabelling, etc. with an example
  here involving decomposition?}

\subsection{Partial equivalences}
\label{sec:subsets}

In what follows we will often make use of constructive evidence that
one type is a ``subset'' of another type, written $A \subseteq B$.  Of
course there is no subtyping in our type theory, so there is no
literal set-theoretic sense in which one type can be a subset of
another. However, we can model this situation with \term{partial
  equivalences}. \todo{cite Tillmann Rendel and Klaus
  Ostermann. Invertible Syntax Descriptions: Unifying Parsing and
  Pretty Printing. In Proc. of Haskell Symposium, 2010. ? Not sure if
  it's really about the same thing, though it may be related somehow.}
A partial equivalence $A \subseteq B$ is given by:
\begin{itemize}
\item a function $|embed| : A \to B$,
\item a function $|project| : B \to 1+A$,
\item a proof that $|project . embed| = \cons{inr}$, and
\item a proof that for all $b : B$, if $|project b| = \cons{inr}(a)$
  then |embed a = b|.
\end{itemize}
That is, there is a 1-1 correspondence between all the elements of $A$
and \emph{some} (possibly all) of the elements of $B$.

Note that an isomorphism $f \mkIso g : A \iso B$ can be made into a
partial equivalence trivially by setting $|embed| = f$ and $|project|
= \cons{inr} \comp g$.  We will not bother to note the conversion,
simply using equivalences as if they were partial equivalences when
convenient.  In addition, note that partial equivalences compose, that
is, we have $- \comp - : (B \subseteq C) \to (A \subseteq B) \to (A
\subseteq C)$, implemented in the obvious way.  Combining the two
previous observations, we can compose an equivalence with a partial
equivalence (or the other way around) to obtain another partial
equivalence.\footnote{Happily, using the Haskell \texttt{lens} library
  \cite{lens}, this all works out automatically: the representations
  of equivalences and partial equivalences (which \texttt{lens} calls
  \emph{prisms}) are such that equivalences simply \emph{are} partial
  equivalences, and they compose as one would expect (albeit
  ``backwards''), using the standard function composition operator.}

% On the other hand, we could drop |project|, that is, we could take
% something like \[ \cons{SubFinite}\ L \defn (n : \N) \times (|embed| :
% L \to \Fin n) \times \cons{Injective}\ |embed|. \] This certainly
% implies that $L$ is finite in a classical sense (\ie not infinite),
% but it does not allow us to construct a $\Finite L$ value.  At the
% moment we are not sure where (or if) this concept might be useful.

\subsection{Mappings, take II}

Idea: change \[ |reindex| : (L' \iso L) \to \Store L A \to \Store {L'} A \]
to \[ |reindex| : (L' \subseteq L) \to \Store L A \to \Store {L'} A \]

Now |reindex| lifts not just equivalences but \emph{partial}
equivalences between labels.  When given an equivalence, |reindex| has
the same semantics as before.  When given a nontrivially partial
equivalence, however, the idea is that |reindex| has the effect of
``forgetting'' part of the mapping. Data associated with labels in $L$
which have no corresponding label in $L'$ are no longer accessible.

The implementation of $\Store L A$ as a function arrow does not need
to change at all.  However, the vector implementation does indeed need
to change, in some interesting ways.  First of all, we store a partial
equivalence instead of an equivalence along with the vector:

\[ \Store L A \defn \sum_{n : \N} (L \iso \Fin n) \times \Vect n A, \]

Note that now the underying vector might have \emph{more} slots than
necessary, which is crucial to be able to implement |reindex|
efficiently.  The implementation of |reindex| still does not need to
allocate, but simply composes the given partial equivalence with the
stored one.
  \begin{spec}
    reindex sub' (n, sub, v) = (n, sub . sub', v)
  \end{spec}

\todo{finish writing about append and concat}

  but what is meant by |sub1 + sub2|?  We need to appropriately
  combine two subset proofs, that is, we need \[ -+- : (L_1 \subseteq
  \Fin {n_1}) \to (L_2 \subseteq \Fin {n_2}) \to (L_1 + L_2) \subseteq
  \Fin {(n_1 + n_2)}. \] It is straightforward to derive $(A_1
  \subseteq B_1) \to (A_2 \subseteq B_2) \to (A_1 + A_2) \subseteq
  (B_1 + B_2)$, so all that remains is to prove $\Fin{n_1} + \Fin{n_2}
  \subseteq \Fin {(n_1 + n_2)}$.  In fact, we actually have the
  stronger property $\Fin{n_1} + \Fin{n_2} \iso \Fin {(n_1 +
    n_2)}$---but there are many such equivalences, and it matters
  which one we pick!  In particular, the correct implementation is
  determined by the behavior of |appendV|.
  \todo{explain more, maybe a picture?}

\subsection{Defragmentation}
\label{sec:defrag}

The type $(n : \N) \times (L \subseteq \Fin n)$ can also be thought of
as a witness of the finiteness of $L$; intuitively, it states that $L$
has size \emph{at most} $n$, which sounds like it would contain
\emph{less} information than a proof $\Finite L$.  However, there is a
lot of information contained in a value of $(L \subseteq \Fin n)$. In
particular, we may use the |project| function to compute the precise
size of $L$.  We can define a function \[ |subToEquiv| : ((n : \N)
\times (L \subseteq \Fin n)) \to ((m : \N) \times (L \iso \Fin m)) \]
by induction on $n$, running the |project| component of $(L \subseteq
\Fin n)$ on each inhabitant of $\Fin n$ and counting how many map to a
value in $L$.

\todo{Actually, there are some interesting choices in how we implement
  |subToEquiv|.  It corresponds in some sense to ``compaction'' or
  ``defragmentation'' if you will, and one might wish to do it with as
  little copying as possible.  The ``naive'' approach, to just ``shift
  everything left'' to fill unused slots may do a lot of unnecessary
  copying.  We can do better using the Gordon Complementary Bijection
  Principle (with type $(A \iso A') \to (A + B \iso A' + B')
  \to (B \iso B')$).  The idea is to prove that for all $s : \N$,
\begin{multline*}
  \left( \sum_{\substack{k : \Fin
        n \\ l : L}} |project|(k) = \cons{inr}(l) \right) + \left(
    \sum_{k : \Fin n} |project|(k) = \inl(\star) \right) \iso
  \Fin n
  \iso \Fin s + \Fin (n - s)
\end{multline*}
where $\Fin (n - s)$ is an abbreviation for $\sum_{j : \N} (j + s = n)
\times \Fin j$; the left-hand equivalence is unique, and for the
right-hand equivalence we want the ``obvious'' implementation which
simply concatenates the elements of $\Fin {(n-s)}$ after those of
$\Fin s$. Then we write a function |Lsize| which simultaneously
computes the size of $L$ and an enumeration of the elements of $\Fin
n$ which do not correspond to elements of $L$: \[ |Lsize| : (n : \N)
\to (L \subseteq \Fin n) \to \sum_{s:\N} \left[ \left( \sum_{k : \Fin
      n} |project|(k) = \cons{inl}(\star) \right) \iso \Fin (n - s)
\right] \] Applying the GCBP now gives us an equivalence \[ \left(
  \sum_{\substack{k : \Fin n \\ l : L}} |project|(k) = \cons{inr}(l)
\right) \iso \Fin s. \] To complete the construction we note that \[ L
\iso \left( \sum_{\substack{k : \Fin n \\ l : L}} |project|(k) =
  \cons{inr}(l) \right) \] by properties of $\subseteq$.  So in the
end we have an equivalence $L \iso \Fin s$ as desired, but one which
``does as little copying as possible'' (it should be possible to
formalize this).
}

\section{Labelled structures}
\label{sec:labelled-formal}

Formally, we may define families of labelled structures as follows:
\begin{align*}
   &\LStr - - - : \Species \to \Type \to \Type \to \Type \\
   &\LStr F L A = F\ L \times \Store L A
\end{align*}
that is, a labelled structure over the species $F$, parameterized by a
type $L$ of labels and a type $A$ of data, consists of
\begin{itemize}
\item a shape of type $F\ L$, \ie\ an $L$-labelled $F$-shape; and
\item a mapping $\Store L A$ from labels to data values (defined
  below).
\end{itemize}

Depending on the representation used for the map type $\Store L A$, a
given labelled structure can have multiple distinct
representations. Ideally, this extra representation detail should be
unobservable when programming with labelled structures. In addition,
species, and hence labelled structures, are functorial in the label
type, so the precise nature of the labels should not be observable
either---that is, computing some function of a labelled structure
should give the same result if we first relabel it.  We can accomplish
this by making the type of labelled structures abstract, and carefully
defining a type of \emph{eliminators} for labelled structures which
hide the extra detail.

\bay{Argh, it just hit me that this story about getting the same
  result before and after relabeling is inconsistent with our story
  about operations on arrays as label operations.  There is something
  more subtle going on here but I am not sure what.}

\subsection{Labelled eliminators}
\label{sec:labelled-eliminators}

The generic type of eliminators for labelled $F$-structures, $\Elim_F
: \Type \to \Type \to \Type$, is defined by
\begin{equation*}
  \Elim_F\ A\ R \defn (L : \Type) \to F\ L \to \DecEq L \to \Store L A \to R
\end{equation*}
where $\DecEq L$ represents decidable equality for $L$. There are a
few subtle issues here which are worth spelling out in detail. First,
note that $\Elim_F$ is parameterized by $A$ (the type of data elements
stored in the labelled structure being eliminated) and $R$ (the type
of the desired result), but \emph{not} by $L$.  Rather, an eliminator
of type $\Elim_F\ A\ R$ must be parametric in $L$; defining an
eliminator which works only for certain label types is not allowed.
The second point is that we assume that $\Store L A$ is held abstract;
an eliminator cannot make use of any details of a particular
implementation for $\Store L A$, but only its abstract interface (in
particular, the |index| function).

Decidable equality on $L$ allows the eliminator to observe value-level
sharing.  If $\DecEq L$ is left out, we have \[ (L : \Type) \to F\ L
\to \Store L A \to R, \] which by parametricity is equivalent to \[ F\
A \to R. \] That is, if we do not observe the sharing (\ie\ if we do not
consult the decidable equality on $L$, to see which labels occur more
than once), then semantically speaking we might as well simply replace
the labels in the $F$-shape with their corresponding $A$ values, and
then eliminate that. However, from an operational point of view, even
without any sharing, filling in the $F$-shape with data might involve
undesirable copying of large amounts of data.

% Including this here for reference (probably doesn't need to actually
% go in the paper):
%
% First note that given an (L |=> A) without knowing anything about L,
% the only thing we can do is apply |index| to turn it into a function.
%
% Free theorem for
%
%   elim :: forall l. f l -> (l -> a) -> r
%
% is
%
%   forall l l', g :: l -> l', x :: f l, p :: l -> a, q :: l' -> a,
%     (forall y :: l. p y = q (g y)) => (f x p = f (fmap g x) q)
%
% Define
%
%   to :: (forall l. f l -> (l -> a) -> r) -> (f a -> r)
%   to f x = f x id
%
%   from :: (f a -> r) -> (forall l. f l -> (l -> a) -> r)
%   from g s p = g (fmap p s)
%
% Then to . from = id  is trivial.  For the other direction,
%
%   from (to f) s p = to f (fmap p s) = f (fmap p s) id = f s p,
%
% where the last step follows from the free theorem, taking l' = a, q =
% id, and g = p.

We can always derive decidable equality for any type with a $\Finite$
proof, by mapping to $\Fin n$ and comparing for equality.  However, we
do not expose the actual $\Finite L$ witness to eliminators.  The
reason is that given a value of $\Finite L$, one can observe an
induced linear order on the elements of $L$, using the usual linear
order on the associated natural numbers. However, this would again
break functoriality: an eliminator would be able to observe some of
the effects of relabeling. Given only $\DecEq L \times (L \to A)$,
there is no way to enumerate the elements of $L$ or observe any order
relation on them.  One can only traverse the shape $F\ L$ and feed
encountered $L$ values into the $(L \to A)$ function to learn the
associated data values, possibly consulting the provided decidable
equality to find out which labels are shared.

Note that if we do want to observe sharing, the given formulation is
not actually very convenient; for example, if we want to know whether
a given label $l : L$ is shared, we have to traverse the entire
$F$-structure and test every label for equality with $l$.  In
practice, there may be equivalent, more operationally convenient
formulations.

We can ``run'' an eliminator,
\[ \elim : \Elim_F\ A\ R \to \LStr F L A \to R, \] by taking apart the
labelled structure and using it to construct the proper arguments to
the eliminator.

\todo{mention in this section that this doesn't give you any help in
  eliminating $F\ L$, which for some species $F$ may be nontrivial
  (\eg anything with symmetry).  Future work.}

\subsection{Zipping and canonical labels}
\label{sec:zipping}

One natural operation on arrays of the same size is to \term{zip}
them, applying some operation to their corresponding elements
pointwise and producing a new array.

Typically, when we think of zipping operation, we think of taking two
values with the ``same shape'' and matching up corresponding elements.
Following this intuition, we could try to define an operation \[
|zip|_F : (L, A, B : \Type) \to \LStr F L A \to \LStr F L B \to \LStr
F L {A \times B} \] by induction on (suitable) algebraic species
descriptions $F$.  However, we quickly get stuck trying to define it
even for binary product, and it is instructive to see why.  We are
given values $x : \LStr {F \sprod G} L A$ and $y : \LStr {F \sprod G}
L B$, and we may assume that we have suitable functions $|zip|_F$ and
$|zip|_G$.  We need to somehow produce a value of type $\LStr {F
  \sprod G} L {A \times B}$.  Expanding the definitions of $\LStr - -
-$ and $\sprod$, we find that $x$ has the type \[ x : \Finite L \times
\sum_{L_1, L_2 : \FinType} \left( (L_1 + L_2 \iso L) \times F\ L_1
  \times G\ L_2 \right) \times \Vect{(\size L)}{A} \] where we have
used $\Sigma$-notation for a dependent pair, to emphasize the fact
that $L_1$ and $L_2$ are existentially quantified within $x$.  $y$ has
a similar type, with $B$ substituted for $A$: \[ y : \Finite L \times
\sum_{L_1', L_2' : \FinType} \left( (L_1' + L_2' \iso L) \times F\
  L_1' \times G\ L_2' \right) \times \Vect{(\size L)}{B} \] However,
we note crucially that $y$ may existentially quantify over types
$L_1'$ and $L_2'$ which are \emph{different} from those in $x$.  We
have nothing on which to apply our inductive hypotheses $|zip|_F$ and
$|zip|_G$, since they require matching label types.  We can put
together the given equivalences to conclude that $L_1 + L_2 \iso L_1'
+ L_2'$, but this still does not tell us anything about the
relationship of $L_i$ to $L_i'$.  Intuitively, the problem is that
though $x$ and $y$ contain the same set of labels, those labels may be
distributed in different ways, and so we have no guarantee that we can
match up the structures in a meaningful way.

\todo{picture of mismatching labelled structures with same shape?}

The takeaway from all of this is that we can only zip two labelled
structures if they have the same shape \emph{labelled in exactly the
  same way}; otherwise, it is not clear how the resulting structure
should be labelled.  However, in general we have no way to ensure
this.

However, there is an alternative, more fundamental way to think about
zipping labelled structures.  We allow zipping only between two bag
structures with the same set of labels, with data corresponding to
matching labels paired in the obvious way.  That is, we have an
operation \[ |zip| : \LStr \E L A \to \LStr \E L B \to
\LStr \E L {A \times B}.\] We can recover a notion of ``shape-based''
zipping by noting that for \term{regular} species (\ie polynomial
functors), we can assign canonical labels based on the shape.
Assigning such canonical labels allows us to then ``forget'' the shape
without losing any information, since the shape is encoded in the labels.

To make this precise, we first introduce an operation |canonicalize|
with a type as follows: \[ |canonicalize| : (F : \RegSpecies) \to
\LStr F L A \to \LStr F {\Path F} A \times (L \iso \Path F) \] That
is, given a regular species $F$, we can relabel an $F$-structure,
returning the canonically relabelled structure (using the canonical
label type $\Path F$) along with an equivalence specifying the
relabeling that was performed.

\todo{Explain $\Path F$.  Also, where to put this definition of
  $\RegSpecies$?}

\begin{flalign*}
  &\Regular : \Species \to \Type \\
  &\Regular F \defn (L, L' : \Type) \to
  (f : F\ L) \to (\sigma : L \iso L') \to ((F\ \sigma\ f = f) \to
  (\sigma = \id))) \\
  &\RegSpecies \defn (F : \Species) \times \Regular F
\end{flalign*}

The problem with the type $\LStr F {\Path F} A$ is that it has
structure duplicated between its shape and the labels.  |canonicalize|
is not itself an equivalence, because given something of type $\LStr F
{\Path F} A$ there is no guarantee that the labels match the
structure in the canonical way---they may be shuffled around.

We therefore introduce another function
\[ |forgetShape| : (F : \Species) \to \LStr F L A \to \LStr \E L A \]
which takes a labelled structure and simply forgets its shape. Also,
given a bag labelled with the canonical labels for some shape, we can
recover the shape: \[ |reconstruct| : (F : \RegSpecies) \to \LStr \E
{\Path F} A \to \LStr F {\Path F} A \] We have the laws \[
|forgetShape| \comp |reconstruct| = id \] \todo{and?}

\todo{finish}
This lets us go back and forth between different views of data.  Some
operations are ``structural'', \ie operate on nontrivial shapes
(\eg matrix multiplication) whereas some (\eg transpose) are best
expressed as operations on structured labels.

% The shape of 2D arrays, for example, is $L_m \comp L_n$ (if we consider 2D
% arrays as a data structure where the ordering of elements is
% significant).  But $Path(L_m \comp L_n) \sim (Fin m, Fin n)$, so we can convert
% between $(Sp (L_m \comp L_n) l a)$ and $(Sp E (Fin m, Fin n) a)$.

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

\section{The algebra of species and labelled structures}
\label{sec:algebraic}

\todo{add eliminators / eliminator combinators for each primitive + operation}

We now return to the observation from \pref{sec:set-species} that we
do not really want to work directly with the definition of species,
but rather with an algebraic theory. In this section we explain such a
theory.  At its core, this theory is not new; what is new is porting
it to a constructive setting, and the introduction and elimination
forms for labelled structures built on top of these species.

Formally, to define a species we must define its action on both label
types and label equivalences.  However, we will only give the actions
on label types: if the action of a species on the label type $L$ is
given by $F\ L$, its action on equivalences $\sigma$ can be derived by
syntactically replacing $L$ by $\sigma$ in the definition of $F$
(using our convention that $F\ \sigma : F\ L_1 \iso F\ L_2$ when
$\sigma : L_1 \iso L_2$). Moreover, this action on equivalences is
automatically functorial.

\subsection{Primitive species}
\label{sec:primitive}

We begin by examining some primitive species which serve as the ``base
cases'' when building up more complex species.

\paragraph{Zero}
  The \emph{zero} or \emph{empty} species, denoted $\Zero$, is the
  unique species with no shapes whatsoever, defined by its action on
  finite types as
  \begin{equation*}
  \Zero\ L = \TyZero
  \end{equation*}
  Of course, it has no introduction form.

\paragraph{One}
The \emph{one} or \emph{unit} species, denoted $\One$, is the species
with a single shape of size $0$ (that is, containing no labels).  The
usual set-theoretic definition is
  \[ \One\ L =
  \begin{cases}
    \{\bullet\} & ||L|| = 0 \\
    \varnothing & \text{otherwise}
  \end{cases}
  \]
  However, this is confusing to the typical type theorist.  First, it
  seems strange that the definition of $\One$ gets to ``look at'' $L$,
  since species are supposed to be functorial.  In fact, the
  definition does not violate functoriality---because it only ``looks
  at'' the size of $L$, not its contents, and bijections preserve
  size---but this is not manifestly obvious. It's also strange that we
  have to pull some arbitrary one-element set out of thin air.

  The corresponding type-theoretic definition, on the other hand, is
  \[ \One\ L = \TyZero \iso L. \] That is, a $\One$-shape consists
  solely of a proof that $L$ is
  empty.\footnote{\citet{Yeh-calculus-virtual-K} mentions something
    equivalent, namely, that the unit species can be defined as the
    hom-functor $\B(\varnothing, -)$, though he certainly does not
    have constructive type theory in mind.}  (Note that there is at
  most one such proof.)

  There is a trivial introduction form for $\One$, also denoted
  $\One$, which creates a $\One$-shape using the canonical label set
  $\Fin\ 0$, that is, \[ \One : \One\ (\Fin\ 0). \] We also have an
  introduction form for labelled $\One$-structures, \[ \lab{\One} : \LStr
  \One {\Fin\,0} A. \]

  In general, species introduction forms will use a canonical label
  type if there is one; other label types may be obtained via
  relabelling.

  \todo{eliminator}

\paragraph{Singleton}
  The \emph{singleton} species, denoted $\X$, is defined by
  \[ \X\ L = \TyOne \iso L, \] that is, an $\X$-shape is just a proof
  that $L$ has size $1$.  Again, there is at most one such proof.
  Unlike $\One$, we may also think of an $\X$-shape as ``containing''
  a single label of type $L$, which we may recover by applying the
  equivalence to $\unit$.

  $\X$-shapes, as with $\One$, have a trivial introduction form,
  \[ \cons{x} : \X\ (\Fin\ 1). \]  To introduce an $\X$-structure, one
  must provide the single value of type $A$ which is to be stored in
  the single location: \[ \lab{\cons{x}} : A \to \LStr \X {\Fin 1} A. \]

  \todo{eliminator}

\paragraph{Sets}
The species of \emph{sets}, denoted $\E$, is defined by \[ \E\ L =
\TyOne. \] That is, there is a single $\E$-shape for every label type.
Intuitively, $\E$-shapes impose no structure whatsoever; that is, a
labelled $\E$-shape can be thought of simply as a \emph{set} of labels.

Note that if $\E$-shapes are sets, then labelled
$\E$-\emph{structures} ($\E$-shapes plus mappings from labels to data)
are \emph{bags}: any particular data element may occur multiple times
(each time associated with a different, unique label).

$\E$-shapes also have a trivial introduction form, $\cons{e} : \E\ L$,
along with a corresponding introduction form for $\E$-structures which
simply requires the mapping from labels to values:
\begin{align*}
\lab{\cons{e}} &: (L \to A) \to \LStr \E L A \\
\lab{\cons{e}} &= |allocate| ...
\end{align*}
\todo{finish}

\todo{eliminator.  Explain why it is problematic.}

As a summary, \pref{fig:prims} contains a graphic showing $\Zero$-,
$\One$-, $\X$-, and $\E$-shapes arranged by size (\ie, the size of the
underlying type of labels $L$): a dot indicates a single shape, and
the size of the label type increases from left to right.

\begin{figure}
  \centering
\begin{diagram}[width='200']
import SpeciesDiagrams

dot = circle 0.2 # fc black
row p     = hcat' (with & sep .~ 0.1) . map (drawOne . p) $ [0..10]
lRow x p  = hcat [text' 1 [x] <> phantom (square 1 :: D R2), strutX 0.5, row p]
drawOne b = square 1 <> mconcat [dot||b]

dia =
  pad 1.1 .
  centerXY .
  vcat' (with & sep .~ 0.3) $
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

It is worth noting that an inverse pair of ``bare'' morphisms, without
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

\subsection{Operations on species and labelled structures}
\label{sec:species-ops}

\todo{say something about how to interpret the picture schemas we will use}

\paragraph{Sum}
Given two species $F$ and $G$, we may form their sum. We use $\ssum$
to denote the sum of two species to distinguish it from $+$, which
denotes a sum of types. The definition is straightforward, and
unsurprising to anyone who has ever done any generic programming: \[
(F \ssum G)\ L = F\ L + G\ L. \] That is, a labelled $(F \ssum G)$-shape is
either a labelled $F$-shape or a labelled $G$-shape (\pref{fig:sum}).

  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F+G"
    , text' 1 "="
    , vcat
      [ struct 5 "F"
      , text' 1 "+"
      , struct 5 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species sum}
    \label{fig:sum}
  \end{figure}

As the reader is invited to check, $(\ssum,\Zero)$ forms a commutative
monoid structure on species, up to species isomorphism.  That is, one
can define natural isomorphisms
\begin{align*}
&\cons{plusAssoc} : \impl{F, G, H : \Species} \to ((F \ssum G) \ssum H
\natiso F \ssum (G \ssum H)) \\
&\cons{zeroPlusL} : \impl{F : \Species} \to (\Zero \ssum F \natiso F) \\
&\cons{plusComm} : \impl{F, G : \Species} \to (F \ssum G \natiso G
\ssum F)
\end{align*}

As expected, there are two introduction forms for $(F \ssum G)$-shapes
and \mbox{-structures}:
\begin{align*}
&\inl : F\ L \to (F \ssum G)\ L \\
&\inr : G\ L \to (F \ssum G)\ L \\
&\lab{\inl} : \LStr F L A \to \LStr {F \ssum G} L A \\
&\lab{\inr} : \LStr G L A \to \LStr {F \ssum G} L A
\end{align*}

\todo{eliminator}

\paragraph{Product}
The product of two species $F$ and $G$ consists of paired $F$- and
$G$-shapes, but with a twist: the label types $L_1$ and $L_2$ used for
$F$ and $G$ are not necessarily the same as the label type $L$
used for $(F \sprod G)$.  In fact, they must constitute a
partition of $L$, in the sense that their sum is isomorphic to $L$ (\pref{fig:product}).
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F•G"
    , text' 1 "="
    , vcat' (with & sep .~ 0.2)
      [ struct 2 "F"
      , struct 3 "G"
      ]
      # centerY
    ]

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species product}
    \label{fig:product}
  \end{figure}
\begin{equation*}
  (F \sprod G)\ L = (L_1, L_2 : \FinType) \times (L_1 + L_2 \iso L) \times F\ L_1 \times G\ L_2
\end{equation*}
For comparison, in set theory the definition is usually presented
as \[ (F \sprod G)\ L = \sum_{L_1 \uplus L_2 = L} F\ L_1 \times G\
L_2 \] which lacks any computational evidence for the relationship of
$L_1$ and $L_2$ to $L$.  The intuition is that each label represents a
unique ``location'' which can hold a data value, so the locations in
the two paired shapes should be disjoint.

Another good way to gain intuition is to imagine indexing species not
by label types, but by natural number sizes.  Then it is easy to see
that we would have \[ (F \sprod G)_n = (n_1, n_2 : \N) \times (n_1 +
n_2 = n) \times F_{n_1} \times G_{n_2}, \] that is, an $(F \sprod
G)$-shape of size $n$ consists of an $F$-shape of size $n_1$ and a
$G$-shape of size $n_2$, where $n_1 + n_2 = n$.  Indexing by labels is
a generalization (a \emph{categorification}, in fact) of this
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
  - \sprod - &: F\ L_1 \to G\ L_2 \to (F \sprod G)\ (L_1 +
  L_2) \\
  - \lab{\sprod} - &: \LStr F {L_1} A \to \LStr G {L_2} A \to
  \LStr {F \sprod G} {L_1 + L_2} A
\end{align*}
\todo{show how to implement $\lab{\sprod}$}

$(\sprod, \One)$ also forms a commutative monoid up to species
isomorphism.

\paragraph{Composition}

We may also define the \term{composition} of two species.
Intuitively, $(F \scomp G)$-shapes consist of a single top-level
$F$-shape, which itself contains labelled $G$-shapes in place of the
usual labels, as illustrated in~\pref{fig:composition}.
Set-theoretically, we have \[ (F \scomp G)\ L = \sum_{\pi \in
  \cons{Par}(L)} F\ \pi \times \prod_{L' \in \pi} G\ L', \] where
$\cons{Par}(L)$ denotes the set of all partitions of $L$ into nonempty
subsets.  Note how this uses the elements of the partition $\pi$
itself as labels on the $F$-structure.  A more natural type-theoretic
encoding is to use an arbitrary type of $F$-labels, and then store a
mapping from these labels to the label types used for the $G$-shapes.
Additionally, we store an equivalence witnessing the fact that the
$G$-labels constitute a partition of the overall label type.
Formally, \[ (F \scomp G)\ L = (L_F : \Type) \times F\ L_F \times
(Ls_G : \StoreNP {L_F} \Type) \times (L \iso \cons{sum}\ Ls_G) \times
\cons{map}\ G\ Ls_G. \]  We assume a function $\cons{sum} : \Store J
\Type \to \Type$ which computes the sum of all the types in the range
of a mapping.

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 6 "F∘G"
    , text' 1 "="
    , drawSpT
      ( nd (text' 1 "F")
        [ struct' 2 "G"
        , struct' 3 "G"
        , struct' 1 "G"
        ]
      ) # centerY
    ]

dia = theDia # centerXY # pad 1.1
  \end{diagram}
  \caption{Species composition}
  \label{fig:composition}
\end{figure}

Composition ($\scomp$), unlike sum ($\ssum$) and product ($\sprod$),
is not commutative\footnote{Interestingly, a recent paper XXX introduces
  XXX which seems to represent a sort of ``commutative composition'';
  XXX future work. \todo{finish}}: an $F$-shape of $G$-shapes is quite different from
a $G$-shape of $F$-shapes.  It is, however, still associative, and in
fact $(\scomp, \X)$ forms a monoid: Intuitively, an ``$F$-shape of
$X$-shapes'' corresponds to an application of |map id| to an
$F$-shape, and ``an $X$-shape of $F$-shapes'' to an application of
|id|.

The space of introduction forms for composition structures is
nontrivial.  We will not separately consider introduction forms for
composition shapes, but study introduction forms for composition
structures directly. At the simplest end of the spectrum, we can
define an operator $\compP$ (``cross'') as a sort of cartesian product
of structures, copying the provided $G$ structure into every location
of the $F$ structure and pairing up both their labels and data
(\pref{fig:compP}):
\begin{equation*}
  - \compP - : \LStr F {L_1} A \to \LStr G {L_2} B \to \LStr {F
  \scomp G} {L_1 \times L_2} {A \times B}
\end{equation*}
\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep.~1)
    [ vcat' (with & sep.~0.2)
      [ nd (text' 1 "F") (map (lf . Lab . Right . show) [3,2,1])
        # drawSpT # centerX
      , text' 1 "⊗"
      , nd (text' 1 "G") (map (lf . Lab . Right . (:[])) "ba")
        # drawSpT # centerX
      ]
      # centerY
    , text' 1 "="
    , nd (text' 1 "F")
      [  nd (text' 1 "G") (map (lf . Lab . Right . (f:)) ["b","a"])
      || f <- "321"
      ]
      # drawSpT
    ]

dia = theDia # centerXY # pad 1.1
  \end{diagram}
  \caption{Constructing a composition with $\compP$}
  \label{fig:compP}
\end{figure}
Of course, this is far from being a general introduction form for
$\scomp$, since it only allows us to construct composition structures
of a special form, but is convenient when it suffices.

We also have $\compA$ (``ap''), defined by
\begin{equation*}
  - \compA - : \LStr F {L_1} {A \to B} \to \LStr G {L_2} A \to \LStr {F
    \scomp G} {L_1 \times L_2} B.
\end{equation*}
$\compA$ is equivalent in power to $\compP$: in particular, |x compP y =
(map (,) x) compA y|, where $(,) : A \to B \to A \times B$ denotes the
constructor for pair types, and |x compA y = map eval (x compP y)|,
where $|eval| : (A \to B) \times A \to B$.  \todo{say something about
  parallel with Haskell's |Applicative| and monoidal functors; cite
  monoidal functors paper I forget}

There is another introduction form for composition ($\compJ$,
``join'') which is a generalization of the |join| ($\mu$) function of
a monad:
\begin{equation*}
  - \compJ - : \LStr F {L_1} {\LStr G {L_2} A} \to \LStr {F \scomp
  G} {L_1 \times L_2} A
\end{equation*}
$\compJ$ takes a labelled $F$-structure filled with labelled
$G$-structures, and turns it into a labelled $(F \scomp G)$-structure.

\todo{illustration for $\compJ$}

$\compJ$, unlike $\compP$ and $\compA$, allows constructing an $(F
\scomp G)$-structure where the $G$-shapes are not all the same.  Note,
however, that all the $G$-structures are restricted to use the same
label set, $L_1$, so they still must all be equal in size.

Most generally, of course, it should be possible to compose
$G$-structures of different shapes and sizes inside an $F$-structure,
which is made possible by $\compB$ (``bind''), the last and most
general introduction form for composition, which can be seen as a
generalization of a monadic bind operation |(>>=)|.
\begin{equation*}
  - \compB - : \LStr F {L_1} A \to ((l : L_1) \to A \to \LStr G
  {L_2\,l} B) \to \LStr {F \scomp G} {(l : L_1) \times L_2\,l} B
\end{equation*}
Here, $L_2$ is actually a \emph{family} of types, indexed over $L_1$,
so each $G$ subshape can have a different type of labels, and hence a
different size.

\todo{illustration for $\compB$}

\paragraph{Cartesian product}

As we saw earlier, the definition of the standard product operation on
species partitioned the set of labels between the two subshapes.
However, there is nothing to stop us from defining a different
product-like operation, known as \term{Cartesian product}, which does
not partition the labels:\[ (F \scprod G)\ L = F\ L \times G\ L \]
This is the ``na\"ive'' version of product that one might expect from
experience with generic programming.

Cartesian product works very differently With labelled shapes,
however.  It is important to remember that a mapping $\Store L A$
still only assigns a single $A$ value to each label; but labels can
occur twice (or more) in an $(F \times G)$-shape.  This lets us
\emph{explicitly} model value-level sharing, that is, multiple parts
of the same shape can all ``point to'' the same data.  In pure
functional languages such as Haskell or Agda, sharing is a (mostly)
unobservable operational detail; with a labelled structure we can
directly model and observe it.

\todo{illustration}

\todo{example}

To introduce a Cartesian product shape, one simply pairs two shapes on
the same set of labels.  Introducing a Cartesian product structure is
more interesting. One way to do it is to overlay an additional shape
on top of an existing structure: \[ \cons{cprodL} : F\ L \to \LStr G L A
\to \LStr {F \scprod G} L A. \] There is also a corresponding
$\cons{cprodR}$ which combines an $F$-structure and a $G$-shape.

$(\scprod, \E)$ forms a commutative monoid up to species isomorphism;
superimposing an $\E$-shape has no effect, since the $\E$-shape
imposes no additional structure.

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
&\OfSize\ F\ n\ L = (\Fin n \iso L) \times F\ L
\end{align*}
The introduction form for $\OfSize$ is simple enough, allowing one to
observe that an existing label type has the size that it has:
\[ \cons{sized} : \Finite L \to \LStr F L A \to \LStr {\OfSize\ F\
  ||L||} L A. \]

We could also generalize to arbitrary predicates on natural numbers,
as in
\begin{align*}
&\OfSize' : \Species \to (\N \to \Type) \to \Species \\
&\OfSize'\ F\ P = \lam{L}{(m : \N) \times P\ m \times (\Fin m \iso L)
  \times F\ L}
\end{align*}
The original $\OfSize$ can be recovered by setting $P\ m \defn (m =
n)$.  However, $\OfSize'$ is difficult to compute with, since $P$ is
an opaque function.  In practice, $P\ m \defn (m \leq n)$ and $P\ m
\defn (m \geq n)$ (along with equality) cover the vast majority of
cases we care about, so as a practical tradeoff we can add explicit
combinators $\cons{OfSizeLTE}$ and $\cons{OfSizeGTE}$ representing these
predicates, with parallel introduction forms:
\begin{align*}
  \OfSizeLTE\ F\ n\ L &= (L \subseteq \Fin n) \times F\ L \\
  \OfSizeGTE\ F\ n\ L &= (L \supseteq \Fin n) \times F\ L
\end{align*}

\paragraph{Derivative and pointing}

The \term{derivative} is a well-known operation on shapes in the
functional programming community~\citep{Huet_zipper,
  mcbride:derivative, abbott_deriv, regular_tree_types,
  mcbride_clowns_2008}, and it works in exactly the way one expects on
species.  That is, $F'$-shapes consist of $F$-shapes with one
distinguished location (a ``hole'') that contains no data.  Formally,
we may define
\[ F'\ L = (L' : \Type) \times (L' \iso \TyOne + L) \times F\ L' \]
\todo{picture}

Note that a mapping $\Store L A$ associates data to every label
in the underlying $F\ L'$ structure but one, since $L' \iso \TyOne +
L$.

To introduce a derivative structure, we require an input structure
whose label type is already in the form $\TyOne + L$:
\begin{align*}
  \cons{d} &: F\ (\TyOne + L) \to F'\ L \\
  \lab{\cons{d}} &: \LStr F {\TyOne + L} A \to A \times \LStr {F'} L A
\end{align*}
The idea with $\lab{\cons{d}}$ is that we get back the $A$ that used
to be labelled by $\TyOne$, paired with a derivative structure with
that value missing.

\todo{talk about down operator, once we have figured out functor composition}

A related operation is that of \term{pointing}.  A pointed $F$-shape
is an $F$-shape with a particular label distinguished. \todo{picture}
Formally,
\[ \pt{F}\ L = L \times F\ L. \]
Introducing a pointed structure simply requires specifying which label
should be pointed:
\begin{align*}
\cons{p} &: L \to F\ L \to \pt{F}\ L \\
\cons{p} &: L \to \LStr F L A \to \LStr{\pt{F}} L A
\end{align*}

The relationship bewteen pointing and derivative is given by the
isomorphism \[ \pt F \natiso \X \sprod F'. \] The right-to-left
direction is straightforward to implement, requiring only some
relabeling.  The left-to-right direction, on the other hand, requires
modelling an analogue of ``subtraction'': the given label type $L$
must be decomposed as ``$(L - l) + l$'' for some $l : L$, that is, \[
L \iso \left(\sum_{l':L} l' \neq l \right) + \left(\sum_{l':L} l' = l
\right). \]

\paragraph{Functor composition}

It is worth mentioning the operation of \emph{functor composition},
which set-theoretically is defined as the ``na\"ive'' composition

\[ (F \fcomp G)\ L = F\ (G\ L). \]

Just as with Cartesian product, functor composition allows encoding
structures with sharing---for example, the species of simple,
undirected graphs can be specified as \[ \mathcal{G} = (\E \sprod \E)
\fcomp (\X^2 \sprod \E), \] describing a graph as a subset ($\E \sprod
\E$) of all ($\fcomp$) ordered pairs chosen from the complete set of
vertex labels ($\X^2 \sprod \E$).

However, functor composition mixes up labels and shapes in the most
peculiar way---and while this is perfectly workable in an untyped,
set-theoretic setting, we do not yet know how to interpret it in a
typed, constructive way.

% Note that the label set given to $F$ is the set of \emph{all $(G\
%   L)$-shapes}.  Giving $G$-shapes as labels for $F$ is the same as
% $\scomp$; the difference is that with $\scomp$ the labels are
% partitioned among all the $G$-shapes, but here the complete set of
% labels is given to each $G$-shape.  This means that a particular label
% could occur \emph{many} times in an $(F \fcomp G)$-shape, since it
% will occur at least once in each $G$-shape, and the $F$-shape may
% contain many $G$-shapes.

% $(\fcomp, \pt{\E})$ forms a (non-commutative) monoid up to species
% isomorphism.

\todo{Give some examples.  Show that we can use recursion from the
  host language.}

% \section{Unlabelled structures}

% \bay{``unlabelled'' is a terrible name for this, we need to come up
%   with a better one.  In any case, the definition is equivalence
%   classes of labelled structures.  Concretely, we always have to work
%   with specific representatives of equivalence classes, and there is
%   not always a nice way to choose a ``canonical'' representative.
%   Instead, we can build relabelling into operations like zip so that
%   some ``conversion'' is done in order to first relabel things so they
%   match.  Such conversion is allowed when working with an equivalence
%   class since it doesn't matter which representative we use.}

\section{Labelled Structures in Haskell}
\label{sec:haskell}

\todo{
  Interesting points of our implementation in Haskell.
  \begin{itemize}
  \item Link to (public) git repo
  \item Heavy use of DataKinds etc. to simulate dep types (cite Hasochism)
  \item Needs to use existentially quantified labels in place of
    dependency, e.g. for $\compB$.
  \item Uses the lens lib for isos and subset.
  \item A lot of overhead; actually compiling such things to efficient
    runtime code is future work.
  \end{itemize}
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
combinators which are possible, we now present a framework for
programming with (arbitrary-dimensional) \emph{arrays}.

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
% have l1-many rows each labelled by l2: all we know is that there are
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

\todo{explain matrix multiplication.}

% Here's how matrix product works.  Recall that 2-dimensional matrices
% have the shape (E . E), where . represents composition.  So I will
% abbreviate the type of 2D matrices containing elements of type a and
% labelled with pairs from the set (Fin m, Fin n) as (E.E) (m,n) a.  Now
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

\subsection{Partition stuff}
\label{sec:partition}

\todo{write about partition, filter, take...?}

\section{Related work}
\label{sec:related}

\begin{itemize}
\item containers, naturally
\item shapely types
\item species in general
\end{itemize}

\section{Future work}
\label{sec:future}

It is worth noting that much of the power of the theory of
species---at least in the context of combinatorics---can be traced to
fruitful homomorphisms between algebraic descriptions of species and
rings of formal power series. \todo{future work making connections to
  computation?}

\todo{extend to $\cons{Countable}\ L = \Finite L + L \iso \N$?}

\todo{assumptions on categories needed for various operations.}

\todo{functor composition}

\todo{Port to Agda, together with proofs of species properties?}

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

\section{Conclusion}
\label{sec:conclusion}

\bibliographystyle{plainnat}
\bibliography{SpeciesAsConstructors}

\end{document}
