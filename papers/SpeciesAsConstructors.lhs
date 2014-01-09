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
\newcommand{\under}[1]{\ensuremath{\left\lfloor #1 \right\rfloor}}
\newcommand{\lift}[1]{\ensuremath{\left\lceil #1 \right\rceil}}

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

\newcommand{\ssum}{\boxplus}
\newcommand{\sprod}{\boxdot}
\newcommand{\scomp}{\boxcircle}
\newcommand{\scprod}{\boxtimes}
\newcommand{\fcomp}{\boxbox}

\newcommand{\LStr}[3]{\langle #1 \rangle_{#2}(#3)}
\newcommand{\LStrE}[2]{\LStr{#1}{\bullet}{#2}}

\newcommand{\compP}{\lab{\otimes}}
\newcommand{\compA}{\lab{\oast}}
\newcommand{\compJ}{\lab{\varovee}}
\newcommand{\compB}{\lab{\varogreaterthan}}

\newcommand{\Vect}[2]{\VectOp\ #1\ #2}

\newcommand{\Path}{\lightning}

\newcommand{\StoreSym}{\Mapsto}
\newcommand{\StoreNP}[2]{\ensuremath{#1 \StoreSym #2}}
\newcommand{\Store}[2]{(\StoreNP{#1}{#2})}

\newcommand{\List}{\mathsf{L}}
\newcommand{\R}{\mathsf{R}}
\newcommand{\Part}{\mathsf{Part}}

\newcommand{\LUO}{$\Lambda$\kern -.1667em\lower .5ex\hbox{$\Upsilon$}\kern -.05em\raise .3ex\hbox{$\Omega$}}

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
  This idea of decomposing container structures into shapes and data
  is an old one; our novel contribution is to explicitly mediate the
  decomposition with arbitrary labels. We demonstrate the benefits of
  this approach in \bay{What actual benefits do we demonstrate now?  I
    think this original list is now out of date: ``implementing and
    reasoning about operations naturally expressed as operations on
    labels, explicitly modelling value-level sharing, and reasoning
    about memory allocation and layout.''}

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


% \scw{I've been thinking about the structure of this paper, trying to make it
% tell its story more effectively.
% The focus of the paper should be on labelled structures. The fact that they
% are directly inspired by combinatorial species is great and should be
% mentioned repeatedly, but in the end, it is not what the paper is about.
% Our introduction mostly works with this format, but we could bring it out.
% I'm imagining a progression like:
% \begin{itemize}
% \item What is a labelled structure? A decomposition of data structure. More
% formally, a labelled shape combined with a mapping from labels to data values.
% \item What is novel about this definition?
% \begin{itemize}
%   \item Labels must be drawn from some finite set, but can have their own
%   structure
%   \item We define the mapping from labels to data values abstractly. It
%     doesn't need to be injective.
% \end{itemize}
% \item What is important about our definition?
% \begin{itemize}
%   \item Non-injective mappings represent sharing in data structures, something
%     that is unobservable for algebraic datatypes.
%   \item Although labels have structure, we make it convenient to work up to (partial)
%     isomorphism. ``Relabelling'' models certain operations on data, sometimes
%     more efficiently that with more standard representations.
%   \item We can choose a definition of mapping that lets us reason about memory
%     allocation and layout.
% \end{itemize}
% \end{itemize}
% However, once we are past the introduction, the story gets muddled. Part of
% this may be that I'm more of a fan of a top-down presentation, whereas the
% current state is more bottom-up. Perhaps we could use more concrete examples
% of what we are trying to do in Section 2 (although explaining them informally)
% before diving into the mathematical preliminaries. Section 3 is called
% ``Cominatorial Species'', though perhaps we should call it ``Labelled
% shapes''. I'm not sure how important it is to start with the set-theoretic
% definition first. Why not start with the real definition, and then later
% explain why it is different in type theory than in set theory?  Are there
% interesting examples of labelled shapes we can give at the end of section 3?
% Or remarks to make about labels?  Section 4 dives into mappings. We present
% mappings as one thing, but then change it to something else in 4.3. Why not
% just start with the definition that we want in the first place?  Section 5
% seems a little strange to me because it starts talking about eliminators
% before talking about where we get labelled structures in the first place
% (Section 6). And section 6 mixes the construction of labelled shapes with the
% construction of labelled structures. Maybe it makes sense to combine these
% explanations, but we need to be more explicit about what we are doing. Sec 6
% also doesn't really connect to the finite map/array examples mentioned
% before. Can we show an example of constructing an array?  }

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
To recover \emph{data} structures, one must add a notion of mapping
from labels to data.  This leads to the familiar idea of decomposing
data structures as shapes plus data \citep{banger1993foundation,
  jay-shapely, ContainerTypesCat, abbott_categories_2003}, with the new 
twist that arbitrary labels are used to mediate between the two.  Informally,
this pairing of a labelled shape (corresponding to a species) and a
mapping from labels to data values is what we call a \term{labelled
  structure}\footnote{Following Flajolet \etal's lead
  \citeyearpar{FlSaZi91,FlajoletZC94}.}.  For example,
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
is assigned to exactly one value. \jc{To me, this is not entirely clear
in the picture.  Wouldn't it be best to separate the boxes for each letter
and have the solid circle and the horizontal rectangle each have arrows
to the S box?}

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
the usual type of trees: every possible labelling of a given tree shape
results in a different labelled structure, whereas there are many
labelled tree structures that will ``collapse'' to the same algebraic
data structure, which differ only in the way they are labelled.

\paragraph{Finite maps and bags}

Since the definition of a labelled structure already includes the
notion of a mapping from labels to data, we may encode finite maps
simply by using \emph{sets} of labels as shapes (\pref{sec:sets}),
\ie\ shapes with no structure other than containing some labels. If we
ignore the labels, the same implementation gives us \emph{bags}, also
known as multisets. Furthermore, we can directly model multiple finite
map implementations.

\paragraph{Vectors and arrays}

Vectors, and multi-dimensional arrays more generally, can be modeled
as finite maps with nontrivial structure on their labels---for
example, 2D arrays have labels from a product type.  Real-world
programs that deal with arrays often care about the precise way in
which the arrays are allocated and laid out in memory. It is possible
to model this as well, but we largely leave that to future work.  In
the present paper, we concentrate on labelled structures with
``trivial'' structure on the labels.

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

\subsection{Contributions}
\label{sec:contributions}

Though our work bears similarities to previous approaches that
separate shapes and data \citep{banger1993foundation, jay-shapely,
ContainerTypesCat, abbott_categories_2003}, there is a key difference, 
directly inspired by the theory of species. Whereas previous approaches 
use a fixed, canonical set of labels (or left the labels entirely implicit),
species naturally lead us to work directly with the labels, giving
them a much more prominent role.  Bringing the mediating labels to the
fore in this way is, to our knowledge, novel, and leads to some
interesting benefits, outlined below.

Furthermore, species are defined over \emph{finite} sets of labels.
In a classical setting, while finiteness is a crucial part of the
definition, it is an otherwise fairly implicit feature of the actual
theory.  Combinatorialists do not need to remind themselves of this
finiteness condition, as it is a pervasive axiom that you can only
``count'' finite collections of objects.  When ported to a
constructive setting, however, the notion of finiteness takes on
nontrivial computational content and significance.  In particular, we
are naturally led to work up to computationally relevant
\emph{equivalences} on labels.  Working up to equivalence in this way
confers additional expressive power, allowing us to model efficient
label operations (\eg partition) without copying.  This is also one of
the key ingredients in modeling memory layout and allocation (\pref{sec:vecmap}).

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
\item We unify ``implicitly labelled'' structures (such as algebraic
  data types) and ``explicitly labelled'' structures (such as vectors
  and finite maps) under the same framework.
\item We show how certain operations (for example, altering the keys 
  of a finite map) can be more naturally described as \emph{operations 
  on labels}, leading to benefits in reasoning---and, we conjecture, to 
  efficiency as well (\pref{sec:programming}).
\item We model value-level \emph{sharing} via shared labels
  (\pref{sec:cartesian-product})---in contrast, this is not possible
  if every structure has a fixed set of canonical labels.
\item In fact, labels share some of the properties of memory
   addresses, \ie\ pointers, and taking this analogy seriously lets us
   reason about memory allocation and layout for stored data
   structures (\pref{sec:vecmap}).
\item We give extended examples showing the utility of labelled types,
  including \todo{?}
\end{itemize}

It is worth mentioning that in previous work \citep{carette_species,
  yorgey-2010-species} we conjectured that the benefits of the theory
of species would lie primarily in its ability to describe data types
with \term{symmetry} (\ie\ quotient types \citep{hofmann1995quotient,
  abbott_quotient}).  That promise has not gone away; but we now
believe that a solid understanding of labelled structures is a
prerequisite for tackling symmetry.  In a sense, this is unsurprising,
since introducing species as explicitly labelled objects was one of
Joyal's great insights, allowing the encoding of symmetric and
unlabelled structures via equivalence classes of labelled ones.

\section{Theoretical setting}
\label{sec:prelim}

We have found it convenient to work within \emph{homotopy type theory}
(HoTT).  However, we do not need much complex machinery from the
theory, and simply summarize the most important ideas and notation
here; interested readers should consult the HoTT book~\citep{hottbook}
for more details.  Everything in this paper could be formalized in
most any standard constructive type theory; we choose to work in HoTT
because of its emphasis on equality and isomorphism, which meshes well
with the theory of species.  In fact, it seems likely that there are
deeper connections between the two theories, but exploring these
connections is left to future work.

The concept of \term{finiteness} plays a central (but implicit) role
in the theory of combinatorial species, primarily through the
pervasive use of generating functions.  As it remains important in our
setting, we give the precise definition we use, seeing as there are
multiple constructive interpretations of finiteness.

\subsection{A fragment of homotopy type theory}
\label{sec:HoTT}

The type theory we work with is equipped with an empty type \TyZero, a
unit type \TyOne (with inhabitant $\unit$), coproducts (with
constructors $\inl$ and $\inr$), dependent pairs (with projections
$\outl$ and $\outr$), dependent functions, a hierarchy of type
universes $\Type_0$, $\Type_1$, $\Type_2$\dots (we usually omit the
subscripts), and a notion of propositional equality.  The theory also
allows inductive definitions.  In particular, we use $\N : \Type_0$ to
denote the type of natural numbers, and $\Fin : \N \to \Type_0$ the
usual indexed type of canonical finite sets.

Instead of writing the traditional $\sum_{x : A} B(x)$ for the type of
dependent pairs and $\prod_{x:A} B(x)$ for dependent functions, we
will often use the Agda-like \citep{Agda} notations $(x:A) \times
B(x)$ and $(x:A) \to B(x)$, respectively (though we still occasionally
use $\Sigma$ and $\Pi$ for emphasis).  We continue to use the standard
abbreviations $A \times B$ and $A \to B$ for non-dependent pair and
function types, that is, when $x$ does not appear free in $B$. Also,
to reduce clutter, we sometimes make use of implicit quantification:
free type variables in a type---like $A$ and $B$ in $A \times (B \to
\N)$---are implicitly universally quantified, like $(A : \Type) \to (B
: \Type) \to A \times (B \to \N)$.

$A \iso B$ is the type of \term{equivalences} between $A$ and $B$;
intuitively, an equivalence is a pair of inverse functions $f : A \to
B$ and $g : B \to A$.\footnote{The precise details are more subtle
  \cite[chap.  4]{hottbook}, but unimportant for our purposes.}  We
overload the notations $\id$ and $\comp$ to denote the identity
equivalence and equivalence composition respectively; we also allow
equivalences of type $A \iso B$ to be implicitly used as functions $A
\to B$ where it does not cause confusion.  We use the notation
$\mkIso$ for constructing equivalences from a pair of functions. That
is, if $f : A \to B$ and $g : B \to A$ are inverse, then $f \mkIso g :
A \iso B$; the proof that $f$ and $g$ are inverse is left implicit.

A few remarks about propositional equality are also in order. First,
the structure of the type theory guarantees that functions are always
functorial with respect to equality, that is, if $e : x = y$ and $f$
is a function of an appropriate type, then $f(x) = f(y)$.  Given $e$
we also have $P(x) \to P(b)$ for any type family $P$, called the
\term{transport} of $P(x)$ along $e$.  Finally, a consequence of the
\emph{univalence axiom} is that an equivalence $A \iso B$ can be
converted to the propositional equality $A = B$ (and vice versa).  The
intuitive idea is to formally encode the common mathematical practice
of treating isomorphic things as identical.  It is important to keep
in mind that an equality $e : A = B$ can thus have nontrivial
computational content.  In other words, $A = B$ means not that $A$ and
$B$ are identical, but merely that they can be used
interchangeably---and moreover, interchanging them may require some
work, computationally speaking.

\subsection{Finiteness}
\label{sec:finiteness}

There are many possible constructive interpretations of finiteness
\citep{finite}; we adopt the simplest: a finite set is one which is in
bijection to a canonical set of a known size. That is,
\[ \Finite A \defn (n : \N) \times (\Fin n \iso A). \]  Other
constructive characterizations of finiteness may have roles to play as
well, but we leave exploring them to future work.

It is tempting to use mechanisms for implicit evidence, such as
Haskell's \emph{type class} mechanism, to record the finiteness of
types.  That is, we could imagine defining a type class
\begin{spec}
class IsFinite a where
  isFinite :: Finite a
\end{spec}
The idea is that the statement ``the type $A$ is finite'' translates
to ``$A$ is an instance of the |IsFinite| class''.  However, this is
not what we want.  An instance $|IsFinite|\ A$ corresponds to a
\emph{canonical choice} of an inhabitant of $\Finite A$, but
inhabitants of $\Finite A$ have nontrivial computational content; it
really matters \emph{which} inhabitant we have.  Thus, instead of
simply passing around types and requiring them to have an implicit,
canonical finiteness proof, we will in general pass around types
\emph{together with} some specific finiteness proof.  We can
encapsulate this by defining \[ \FinType \defn (A : \Type) \times
\Finite A \] as the universe of finite types. We use $\under - :
\FinType \to \Type$ to project out the underlying type from a finite
type, forgetting the finiteness evidence.  We also use $\lift{\Fin n}
: \FinType$ to denote the type $\Fin n : \Type$ paired with the
identity equivalence.

It is not hard to see that the size of a finite type is determined
uniquely. That is, if $(n_1,e_1)$ and $(n_2,e_2) : \Finite A$ are any
two witnesses that $A$ is finite, then $n_1 = n_2$.  As proof, note
that $e_2^{-1} \comp e_1 : \Fin{n_1} \iso \Fin{n_2}$, from which we
can derive $n_1 = n_2$ by double induction. In a slight abuse of
notation, we write $\size{A}$ to denote this size.  Computationally,
this corresponds to applying $\outl$ to some finiteness proof; but
since it does not matter which proof we use, we simply leave it
implicit, being careful to only use $\size -$ in a context where a
suitable finiteness proof can be obtained.  We also write $\size L$
when $L : \FinType$, to denote the projection of the natural number size
stored in $L$.

As a final remark, we note that an inhabitant of $\Finite A$ contains
quite a lot of information, much more than one usually means by saying
``$A$ is finite''.  For example, it encodes a total order and
decidable equality on $A$, by transferring these properties along the
equivalence from $\Fin n$.  This is often useful, but occasionally it
gets us into trouble (\pref{sec:sets}).  It may be that the right
evidence for the finiteness of $A$ is not $(n : \N) \times (\Fin n
\iso A)$ but the \term{propositional truncation} \[ (n : \N) \times
\|| \Fin n \iso A \||, \] or something like it
\cite[sect. 3.7]{hottbook}. In any case, we are reasonably certain
that a complete story of labelled structures with symmetries will
require a more nuanced conception of evidence for finiteness; we leave
this to future work.

\section{Combinatorial Species}
\label{sec:species}

Our theory of labelled structures is inspired by, and directly based
upon, the theory of \term{combinatorial species} \citep{joyal}.  We
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
\item sends any finite set $L$ (of \term{labels}) to a set
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
\Set$, where $\B$ is the category of finite sets whose morphisms
are bijections, and $\Set$ is the usual category of sets whose
morphisms are arbitrary (total) functions.  Note that we could have
chosen $\FinSet$ as codomain with very few changes, but $\Set$ is now
customary.

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
data associated to the labels) and bare labelled \emph{shapes}
(which do not).

Here we see that the formal notion of ``shape'' is actually quite
broad, so broad as to make one squirm: a shape is just an element of
some arbitrary set!  In practice, however, we are interested not in
arbitrary species but in ones built up algebraically from a set of
primitives and operations.  In that case the corresponding shapes will
have more structure as well; we explore this in \pref{sec:algebraic}.
For the moment, we turn to a constructive, type-theoretic definition
of species.

\subsection{Species, constructively}
\label{sec:constructive-species}

The foregoing set-theoretic definition of species is perfectly
serviceable in the context of classical combinatorics, but in order to
use it as a foundation for data structures, it is necessary to first
``port'' the definition from set theory to constructive type theory.
In fact, doing so results in a greatly simplified definition: we
merely define \[ \Species \defn \FinType \to \Type. \] The rest of the
definition comes ``for free'' from the structure of our type theory!
In particular, we have \[ \relabel : (F : \Species) \to (L_1 = L_2)
\to (F\ L_1 \to F\ L_2) \] via transport, where $\relabel$
automatically respects identity and composition. This is one of the
great strengths of type theory as a foundation for mathematics:
everything is functorial, natural, continuous, \dots, and we do not
have to waste time ruling out bizarre constructions which violate
these obvious and desirable properties, or proving that our
constructions do satisfy them.

It is important to note that an equality $L_1 = L_2$ between
constructively finite types $L_1,L_2 : \FinType$, as required by
$\relabel$, contains more than first meets the eye.  Since \[ \FinType
\defn (L : \Type) \times (n : \N) \times (\Fin n \iso L), \] such
equalities contain not just an equality $\under{L_1} = \under{L_2}$
between the underlying types (typically constructed from an
equivalence $\under{L_1} \iso \under{L_2}$ via univalence), but also
an equality between their sizes, and a second-order
equality-between-equivalences requiring the types to be isomorphic to
$\Fin n$ ``in the same way'', that is, to yield the same equivalence
with $\Fin n$ after mapping from one to the other.  The situation can
be pictured as shown in \pref{fig:fin-equiv}, where the diagram
necessarily contains only triangles: corresponding elements of $L_1$
and $L_2$ on the sides correspond to the same element of $\Fin n$ on
the bottom row.
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
Intuitively, this means that if $L_1, L_2 : \FinType$, an equality
$L_1 = L_2$ cannot contain ``too much'' information: it only tells
us how the underlying types of $L_1$ and $L_2$ relate, preserving the
fact that they can both be put in correspondence with $\Fin n$ for
some $n$.  In particular, it cannot also encode a nontrivial
permutation on $\Fin n$.

\section{Labelled structures and mappings}
\label{sec:mappings}

To recover a notion of \emph{data structure}, we must pair species,
\ie labelled shapes, with mappings from labels to data.
Formally, we define families of labelled structures by
\begin{align*}
   &\LStr - - - : \Species \to \Type \to \Type \to \Type \\
   &\LStr F L A = F\ L \times \Store L A
\end{align*}
where $\StoreNP - - : \FinType \to \Type \to \Type$ constructs the type
of \term{mappings}. We need not pin down a particular implementation
for $\StoreNP - -$; we require only that it come equipped with the
following operations:
\begin{align*}
  |allocate| &: (\under L \to A) \to \Store L A \\
  |index|  &: \Store L A \to \under L \to A \\
  |map| &: (A \to B) \to \Store L A \to \Store L B \\
  |reindex| &: (L' \iso L) \to \Store L A \to \Store {L'} A \\
  |zipWith| &: (A \to B \to C) \to \Store L A \to \Store L B \to \Store L C \\
  |append| &: (\under{L_1} + \under{L_2} \iso \under{L}) \to \Store {L_1} A \to \Store {L_2} A \to \Store L A \\
  |concat| &: (\under{L_1} \times \under{L_2} \iso \under{L}) \to \Store {L_1} {\Store {L_2} A} \to \Store L A
\end{align*}
One could also imagine requiring other operations like $|replace| : L
\to A \to \Store L A \to A \times \Store L A$, but these are the
operations we need in the context of this paper. The semantics of
these operations can be specified by various laws (for example,
|allocate| and |index| are inverse; |index| and |reindex| commute
appropriately with the other operations; and so on). For now, we will
content ourselves with some informal descriptions of the semantics.

\begin{itemize}
\item First, |allocate| is the sole means of constructing $\Store L A$
  values, taking a function $\under L \to A$ as a specification of the
  mapping. Note that since $L : \FinType$, implementations of
  |allocate| also have access to an equivalence $\under L \iso \Fin
  {\size L}$.  Intuitively, this is important because allocation may
  require some intensional knowledge about the type $L$.  For example,
  as explained in~\pref{sec:vecmap}, we may implement $\Store L A$
  using a vector of $A$ values; allocating such a vector requires
  knowing the size of $L$.
\item |index| allows looking up data by label.
\item |map| ensures that $\Store L -$ is functorial.
\item $|reindex| : (L' \iso L) \to \Store L A \to \Store {L'} A$
  expresses the functoriality of $\Store - A$: we can change from one
  type of labels to another by specifying an equivalence between
  them. |map| and |reindex| together thus give $\Store - -$ the
  structure of a profunctor.
\item |zipWith| gives us a way to combine the contents of two mappings
  labelwise.
\item |append| and |concat| are ``structural'' operations, allowing us
  to combine two mappings into one, or collapse nested mappings,
  respectively. One might na\"ively expect them to have types like
  $|append| : \Store {L_1} A \to \Store {L_2} A \to \Store {(L_1 +
    L_2)} A$, but this is not even well-typed: $L_1$ and $L_2$ are
  elements of $\FinType$, not $\Type$, and there is no obvious way to
  lift $+$ to operate over $\FinType$.  In particular, there are many
  possible ways to combine equivalences $\under{L_1} \iso
  \Fin{\size{L_1}}$ and $\under{L_2} \iso \Fin{\size{L_2}}$ into an
  equivalence $\under{L_1} + \under{L_2} \iso \Fin{(\size{L_1} +
    \size{L_2})}$, and no canonical way to pick one. (Should the
  elements of $L_1$ come first? $L_2$? Should they be interleaved
  somehow?) Intuitively, the extra argument to |append| provides
  precisely this missing information (and similarly for |concat|).
\end{itemize}

% The keen-eyed, categorically-oriented reader might well notice that
% these encode properties of the functor category
% $\left[\FinSet,C\right]$, for an arbitrary category $C$, except for
% $|allocate|$ which requires more structure.  $|allocate|$ bears close
% resemblance to the Yoneda embedding, which is why $\Set$ is nowadays
% chosen as the codomain for species. \bay{This paragraph is too terse;
%   I don't really understand it.  Can you elaborate a bit?}

We can give a particularly simple implementation with $\Store L A
\defn \under L \to A$, presented here using Haskell-like notation:

\begin{spec}
  allocate         = id
  index            = id
  map              = (.)
  reindex i f      = f . i
  zipWith z f g    = \l -> z (f l) (g l)
  append e f g     = either f g . inv(e)
  concat e f       = curry f . inv(e)
\end{spec}

Note that this implementation of |allocate| does not take into account
the finiteness of $L$ at all.  In~\pref{sec:vecmap} we explore a more
interesting implementation which does make use of the finiteness of
$L$.

\section{The algebra of species and labelled structures}
\label{sec:algebraic}

We now return to the observation from \pref{sec:set-species} that we
do not really want to work directly with the definition of species,
but rather with an algebraic theory. In this section we explain such a
theory.  At its core, this theory is not new; what is new is porting
it to a constructive setting, and the introduction and elimination
forms for labelled structures built on top of these species.

\subsection{Algebraic data types}
\label{sec:primitive}

We begin by exhibiting species, \ie labelled shapes, which
correspond to familiar algebraic data types. As a visual aid,
throughout the following section we will use schematic illustrations
as typified in~\pref{fig:species-schematic}.  The edges of the tree
visually represent different labels; the leaves of the tree represent
data associated with those labels.  The root of the tree shows the
species shape applied to the labels (in this case, $F$).
\begin{figure}
  \centering
  \begin{diagram}[width=100]
import SpeciesDiagrams

dia = nd (text' 1 "F") [ lf' (sLabels !! l) (Leaf (Just $ leafData l)) || l <- [0..2] ]
    # drawSpT # centerXY # pad 1.1
  \end{diagram}
  %$
  \caption{Schematic of a typical $(F\ L)$-structure}
  \label{fig:species-schematic}
\end{figure}

\paragraph{Zero}
The \emph{zero} or \emph{empty} species, denoted $\Zero$, is the
unique species with no shapes whatsoever, defined by
  \begin{equation*}
  \Zero\ L \defn \TyZero.
  \end{equation*}

\paragraph{One}
The \emph{one} or \emph{unit} species, denoted $\One$, is the species
with a single shape of size $0$ (that is, containing no labels),
defined by
\[ \One\ L \defn (\TyZero = L). \] That is, a $\One$-shape with labels
drawn from $L$ consists solely of a proof that $L$ is
empty.\footnote{\citet{yeh-k-species} mentions something equivalent,
  namely, that the unit species can be defined as the hom-functor
  $\B(\varnothing, -)$, though he certainly does not have constructive
  type theory in mind.}  (Note that there is at most one such proof.)

There is a trivial introduction form for $\One$, also denoted $\One$,
which creates a $\One$-shape using the canonical label set
$\lift{\Fin\ 0} : \FinType$, that is, \[ \One : \One\ \lift{\Fin\
  0}. \] We also have an introduction form for labelled
$\One$-structures, \[ \lab{\One} : \LStr \One {\lift{\Fin 0}} A. \]

  Note that the usual set-theoretic definition is
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

\paragraph{Singleton}
  The \emph{singleton} species, denoted $\X$, is defined by
  \[ \X\ L \defn (\TyOne = L), \] that is, an $\X$-shape is just a proof
  that $L$ has size $1$.  Again, there is at most one such proof.
  Unlike $\One$, we may also think of an $\X$-shape as ``containing''
  a single label of type $L$, which we may recover by applying the
  equivalence to $\unit$.

  $\X$-shapes, as with $\One$, have a trivial introduction form,
  \[ \cons{x} : \X\ \lift{\Fin\ 1}. \] To introduce an $\X$-structure, one
  must provide the single value of type $A$ which is to be stored in
  the single location: \[ \lab{\cons{x}} : A \to \LStr \X {\lift{\Fin 1}}
  A. \]

  Combinatorialists often regard the species $\X$ as a ``variable''.
  Roughly speaking, this can be justified by thinking of the inhabitant
  of $L$ as the actual variable, and the species $\X$ then
  \emph{represents} the action of subtituting an arbitrary value for
  that label in the structure.  In that sense $\X$ does act operationally
  as a variable.  However, $\X$ does \emph{not} act like a binder.

\paragraph{Sum}
Given two species $F$ and $G$, we may form their sum. We use $\ssum$
to denote the sum of two species to distinguish it from $+$, which
denotes a sum of types. The definition is straightforward: \[ (F \ssum
G)\ L \defn F\ L + G\ L. \] That is, a labelled $(F \ssum G)$-shape is
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
can define equivalences
\begin{align*}
  \cons{plusAssoc} &: (F \ssum G) \ssum H
  \iso F \ssum (G \ssum H) \\
  \cons{zeroPlusL} &: \Zero \ssum F \iso F \\
  \cons{plusComm} &: F \ssum G \iso G \ssum F
\end{align*}
We remark that unfolding definitions, an equivalence $F \iso G$
between two $\Species$ is seen to be a natural isomorphism between $F$
and $G$ as functors; this is precisely the usual definition of
isomorphism between species.

As expected, there are two introduction forms for $(F \ssum G)$-shapes
and \mbox{-structures}:
\begin{align*}
&\inl : F\ L \to (F \ssum G)\ L \\
&\inr : G\ L \to (F \ssum G)\ L \\
&\lab{\inl} : \LStr F L A \to \LStr {F \ssum G} L A \\
&\lab{\inr} : \LStr G L A \to \LStr {F \ssum G} L A
\end{align*}

As a simple example, the species $\One \ssum \X$ corresponds to the
familiar |Maybe| type from Haskell, with $\lab{\inl} \lab{\One}$
playing the role of |Nothing| and $\lab{\inr} \comp \lab{\cons{x}}$
playing the role of |Just|.  Note that $\LStr {\One \ssum \X} L A$ is
only inhabited for certain $L$ (those of size $0$ or $1$), and moreover that
this size restriction determines the possible structure of an inhabitant.

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
  (F \sprod G)\ L \defn \sum_{L_1, L_2 : \FinType} (\under{L_1} + \under{L_2} \iso \under{L}) \times F\ L_1 \times G\ L_2
\end{equation*}
For comparison, in set theory the definition is usually presented
as \[ (F \sprod G)\ L = \sum_{L_1 \uplus L_2 = L} F\ L_1 \times G\
L_2 \] which is obviously similar, but lacks any computational
evidence for the relationship of $L_1$ and $L_2$ to $L$.

The intuition behind partitioning the labels in this way is that each
label represents a unique ``location'' which can hold a data value, so
the locations in the two paired shapes should be disjoint. Another
good way to gain intuition is to imagine indexing species not by label
types, but by natural number sizes.  Then it is easy to see that we
would have \[ (F \sprod G)_n \defn \sum_{n_1, n_2 : \N} (n_1 + n_2 = n)
\times F_{n_1} \times G_{n_2}, \] that is, an $(F \sprod G)$-shape of
size $n$ consists of an $F$-shape of size $n_1$ and a $G$-shape of
size $n_2$, where $n_1 + n_2 = n$.  Indexing by labels is a
generalization (a \emph{categorification}, in fact) of this
size-indexing scheme, where we replace natural numbers with finite
types, addition with coproduct, and multiplication with product.

Finally, this definition highlights a fundamental difference between
\emph{container types} and \emph{labelled shapes}.  Given two functors
representing container types, their product is defined as $(F \times
G)\ A = F\ A \times G\ A$---that is, an $(F\times G)$-structure
containing values of type $A$ is a pair of an $F$-structure and a
$G$-structure, both containing values of type $A$.  On the other hand,
when dealing with labels instead of data values, we have to carefully
account for the way the labels are distributed between the two shapes.

One introduces a labelled $(F \sprod G)$-shape by pairing a labelled
$F$-shape and a labelled $G$-shape, using a label set isomorphic to
the coproduct of the two label types:
\begin{align*}
  - \sprod_- - &: (\under{L_1} + \under{L_2} \iso \under{L}) \to F\ L_1
  \to G\ L_2 \to (F \sprod G)\ L \\
  - \lab{\sprod}_- - &: (\under{L_1} + \under{L_2} \iso \under{L}) \to \LStr F {L_1} A \to \LStr G {L_2} A \to
  \LStr {F \sprod G} L A
\end{align*}
We use here (and for the rest of the paper) the notational convention that
the isomorphism arguments are given first, but are written as subscripts
in mathematical notation. 

As an example, we may now encode the standard algebraic data type of
lists, represented by the inductively-defined species satisfying
$\List \iso \One \ssum (\X \sprod \List)$ (for convenience, in what
follows we leave implicit the constructor witnessing this
equivalence).  We can then define the usual constructors $\cons{nil}$
and $\cons{cons}$ as follows:
\begin{align*}
  &\cons{nil} : \LStr{\List}{\Fin 0} A \\
  &\cons{nil} \defn \lab{\inl} \lab{\One} \\
  &\cons{cons} : A \to \LStr \List L A \to (\Fin 1 + \under L \iso
  \under{L'}) \to \LStr \List {L'} A \\
  &\cons{cons}\ a\ (|shape|,|elts|)\ e \defn (\inr\ (\cons{x} \sprod_e
  |shape|), |append|\ e\ (|allocate|\ (\lambda x. a))\ |elts|)
\end{align*}
The interesting thing to note here is the extra equivalence passed as
an argument to $\cons{cons}$, specifying the precise way in which the
old label type augmented with an extra distinguished label is
isomorphic to the new label type.  Again, one might intuitively expect
something like \[ \cons{cons} : A \to \LStr \List L A \to \LStr \List
{\lift{\Fin 1} + L} A, \] but this is nonsensical: we cannot take the
coproduct of two elements of $\FinType$, as it is underspecified.  For
implementations of $\StoreNP - -$ which make use of the equivalence to
$\Fin n$ stored in $\FinType$ values (we give an example of one such
implementation in \pref{sec:vecmap}), the extra equivalence given as
an argument to \cons{cons} allows us to influence the particular way
in which the list elements are stored in memory.  For lists, this is 
not very interesting, and we would typically use a variant $\cons{cons'} 
: A \to \LStr \List L A \to \LStr \List {\cons{inc}(L)} A$ making use of a
canonical construction $\cons{inc}(-) : \FinType \to \FinType$ with
$\Fin 1 + \under L \iso \under{\cons{inc}(L)}$.

\todo{What else needs to be said about lists? e.g. converting to and
  from Haskell lists?  generic eliminators?}
\jc{Mentioning that we can go to-and-fro would be good.  But maybe
punt on eliminators until the section where we talk about them?}

\subsection{Composition}
\label{sec:composition}

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
Formally, \[ (F \scomp G)\ L \defn \sum_{L_F : \Type} F\ L_F \times
(Ls_G : \StoreNP {L_F} \FinType) \times (\under L \iso |sum|\ (|map|\
\under{-}\ Ls_G)) \times |prod|\ (|map|\ G\ Ls_G). \] We assume
functions $|sum|, |prod| : \Store J \Type \to \Type$ which compute the
sum and product, respectively, of all the types in the range of a
mapping.

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
is not commutative\footnote{Interestingly, a relatively recent paper
  of \citet{Maia2008arithmetic} introduces a new monoidal structure on
  species, the \term{arithmetic product}, which according to one
  intuition represents a sort of ``commutative composition''.
  Incorporating this into our framework will, we conjecture, have
  important applications to multidimensional arrays.}: an $F$-shape of
$G$-shapes is quite different from a $G$-shape of $F$-shapes.  It is,
however, still associative, and in fact $(\scomp, \X)$ forms a monoid.

The space of introduction forms for composition structures is
nontrivial.  We will not separately consider introduction forms for
composition shapes, but study introduction forms for composition
structures directly. At the simplest end of the spectrum, we can
define an operator $\compP$ (``cross'') as a sort of cartesian product
of structures, copying the provided $G$ structure into every location
of the $F$ structure and pairing up both their labels and data
(\pref{fig:compP}):
\begin{equation*}
  - \compP_- - : (\under{L_1} \times \under{L_2} \iso \under L) \to \LStr F {L_1} A \to \LStr G {L_2} B \to \LStr {F
  \scomp G} L {A \times B}
\end{equation*}
The isomorphism argument is notated as a subscript to $\compP$.
\begin{figure}
  \centering
  \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep.~1)
    [ vcat' (with & sep.~0.2)
      [ nd (text' 1 "F") [ lf' (sLabels !! l) (Leaf (Just $ leafData l)) || l <- [0..2] ]
        # drawSpT # centerX
      , text' 1 "⊗"
      , nd (text' 1 "G") [ lf' (sLabels !! l) (Leaf (Just $ leafData l)) || l <- [3..4] ]
        # drawSpT # centerX
      ]
      # centerY
    , text' 1 "="
    , nd (text' 1 "F")
      [  nd' (sLabels !! f) (text' 1 "G") [ lf' (sLabels !! g) (Leaf (vcat' (with & sep .~ 0.1) <$> mapM (Just . leafData) [f,g])) || g <- [3,4]]
      || f <- [0..2]
      ]
      # drawSpT
    ]

dia = theDia # centerXY # pad 1.1
  \end{diagram}
  %$
  \caption{Constructing a composition with $\compP$}
  \label{fig:compP}
\end{figure}
Of course, this is far from being a general introduction form for
$\scomp$, since it only allows us to construct composition structures
of a special form, but is convenient when it suffices.

We also have $\compA$ (``ap''), with type
\begin{equation*}
  - \compA_- - : (\under{L_1} \times \under{L_2} \iso \under L) \to \LStr F {L_1} {A \to B} \to \LStr G {L_2} A \to \LStr {F
    \scomp G} L B.
\end{equation*}
$\compA$ is equivalent in power to $\compP$: in particular, |x compP y =
(map (,) x) compA y|, where $(,) : A \to B \to A \times B$ denotes the
constructor for pair types, and |x compA y = map eval (x compP y)|,
where $|eval| : (A \to B) \times A \to B$.

% \todo{say something about
%   parallel with Haskell's |Applicative| and monoidal functors; cite
%   monoidal functors paper I forget}

There is another introduction form for composition ($\compJ$,
``join'') which is a generalization of the |join| ($\mu$) function of
a monad:
\begin{equation*}
  - \compJ - : (\under{L_1} \times \under{L_2} \iso \under L) \to \LStr F {L_1} {\LStr G {L_2} A} \to \LStr {F \scomp
  G} L A
\end{equation*}
$\compJ$ takes a labelled $F$-structure filled with labelled
$G$-structures, and turns it into a labelled $(F \scomp G)$-structure.

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
  - \compB_- - : \left(\sum_{l : \under{L_1}} \under{L_2\ l} \right) \iso \under
    L \to \LStr F {L_1} A \to \left(\prod_{l : L_1} A \to \LStr G
  {L_2\ l} B\right) \to \LStr {F \scomp G} L B
\end{equation*}
Here, $L_2$ is actually a \emph{family} of types, indexed over $L_1$,
so each $G$ subshape can have a different type of labels, and hence a
different size (\pref{fig:compB}).

\begin{figure}
  \centering
  \begin{diagram}[width=250]
import           Control.Arrow                  (first)
import           Data.Tree
import           Diagrams.Prelude hiding (arrow)
import           SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ vcat' (with & sep .~ 0.5)
      [ nd (text' 1 "F") [ lf' (sLabels !! l) (Leaf (Just $ leafData l)) || l <- [0..2] ]
        # drawSpT # centerX
      , bindOp # scale 0.2 # lw 0.03
      , cat' unitY (with & sep .~ 0.3)
        [ mkMapping l l (drawSpT g) || (l,g) <- zip [0..2] gs ]
        # centerXY
      ]
      # centerY
    , text' 1 "="
    , nd (text' 1 "F") (zipWith labelSp [0..2] gs)
      # drawSpT
    ]
  where
    labelSp l (Node (_,n) ts) = Node (Just (sLabels !! l), n) ts

bindOp :: Diagram B R2
bindOp = circle 1 <> joiner # clipBy (circle 1)
  where
    joiner = fromOffsets [unitX, unitY]
           # rotateBy (1/8)
           # scaleY (1/2)
           # sized (Width 2)
           # centerXY

gs :: [SpT]
gs = map mkG [[0,1],[2],[3,4]]
  where
    mkG ls = nd (text' 1 "G") [ lf' (sLabels !! l) (Leaf (Just $ leafData (3+l))) || l <- ls ]

mkMapping l a g =
  hcat' (with & sep .~ 0.3)
    [ (sLabels !! l) origin (0.5 ^& 0) |||||| leafData a
    , arrow 0.5 mempty
    , g
    ]

dia = theDia # centerXY # pad 1.1
  \end{diagram}
  %$
  \caption{Constructing a composition with $\compB$}
  \label{fig:compB}
\end{figure}

As an example using composition, we can directly encode the type of
ordered, rooted $n$-ary trees, sometimes known as \term{rose trees},
as $\R \iso \X \sprod (\List \scomp \R)$.  This corresponds to the
Haskell type |Rose| defined as |data Rose a = Node a [Rose a]|.
The explicit use of composition is useful when doing generation of such
structures, as it allows switching of generation strategies at
those points~\citep{UszkayThesis}.

The most general type for the \cons{node} constructor is complex,
since it must deal with a list of subtrees all having different label
types.  As a compromise, we can make use of a variant type
representing labelled structures with an existentially quantified
label type:
\[ \LStrE F A \defn \sum_{L : \FinType} \LStr F L A \]
Using $\LStrE \R A$, we can write a constructor for $\R$ as follows:
\[ \cons{nodeE} : A \to [\LStrE \R A] \to \LStrE \R A \]

\todo{finish.  Make a picture?  Is the above even correct?  Is there
  anything interesting to say about what we get from composition?}
\jc{I don't think we need a picture.  It looks correct.  I added something
about what we get from composition.}

\subsection{Sets, bags, and maps}
\label{sec:sets}

The species of \emph{sets}, denoted $\E$, is defined by \[ \E\ L \defn
\TyOne. \] That is, there is a single $\E$-shape for every label type.
Intuitively, $\E$-shapes impose no structure whatsoever; that is, a
labelled $\E$-shape can be thought of simply as a \emph{set} of
labels.  This is the first example of a species with nontrivial
\term{symmetry}, \ie which is invariant under some nontrivial
permutations of the labels.  In fact, $\E$ is invariant under
\emph{all} label permutations.  It is thus the ``quintessential''
symmetric species.  Anecdotally, introducing $\E$ alone seems to go a
very long way towards enabling the sorts of symmetric structures that
actually arise in programming; we give some examples below. (Adding
the species $\Cyc$ of \term{cycles} covers almost all the rest, but we
do not consider cycles in this paper.)

Note that if $\E$-shapes are sets, then labelled $\E$-structures
($\E$-shapes plus mappings from labels to data) are \term{bags}, or
\term{multisets}: any particular data element may occur multiple times
(each time associated with a different, unique label), and the
collection of data elements has no structure imposed on it.

$\E$-shapes have a trivial introduction form, $\cons{e} : \E\ L$,
along with a corresponding introduction form for $\E$-structures which
simply requires the mapping from labels to values:
\begin{align*}
&\lab{\cons{e}} : (\under L \to A) \to \LStr \E L A \\
&\lab{\cons{e}} f = (\unit, |allocate|\ f)
\end{align*}

Eliminating $\E$-structures, on the other hand, is somewhat
problematic.  At the end of the day, the data need to be stored in
some particular order in memory, but we do not want to allow any such
ordering to be observed.  We can require $\E$-structures to be
eliminated using a commutative monoid, but if an eliminator has access
to the finiteness proof for the label type, it can still observe a
linear ordering on the labels and hence on the data elements as well.
As a ``solution'', we could forbid eliminators from being able to
observe labels, but this largely defeats the purpose of having
explicitly labelled structures in the first place.  In the end, this
is a problem needing more study, likely requiring a rethinking of the
way we represent evidence of finiteness.

Leaving the problems with the mechanics of elimination aside for the
moment, we highlight here a few particular examples of the use of
$\E$:

\paragraph{Rooted, unordered trees}
If we replace the $\List$ in the definition of rose trees with $\E$,
we obtain a species of rooted, arbitrary-arity trees where the
children of each node are \emph{unordered}: \[ \T \iso \X \sprod (\E
\scomp \T). \]  Hierarchies without an ordering on sibling nodes arise
quite often in practice: for example, filesystem directory hierarchies
and typical company organizational charts are both of this type.

\paragraph{Finite maps} Formally, there is no difference between bags
(multisets) and finite maps: both may be represented by $\LStr \E L
A$.  The difference is the role played by the labels.  With bags, the
labels are implicit; indeed, we might wish to define $|Bag|\ A \defn
\sum_{L : \FinType} \LStr \E L A$.  With finite maps, on the other
hand, the labels play a more explicit role.

There are many possible implementations of finite maps, with attendant
performance tradeoffs.  We can explicitly model different
implementations with suitable implementations of $\StoreNP - -$.
\pref{sec:vecmap} gives one implementation (and hints at another),
corresponding to finite maps stored as arrays or tries.  Another
common class of finite map implementations involve a balanced tree,
making use of a required total ordering on the labels.  It should be
easy to model such implementations as well, by extending the framework
in this paper to allow arbitrary extra structure on label types.

\paragraph{Partition} We may define the species $\Part$ of
\term{partitions} by \[ \Part \defn \E \sprod \E. \] $(\Part\
L)$-shapes consist of a (disjoint) pair of sets of labels.  Thus
$(\Part\ L)$-shapes represent \emph{predicates} on labels, \ie they
are isomorphic to $\under L \to 2$.  In conjunction with Cartesian
product (\pref{sec:cartesian-product}), this allows us to generalize
operations like |filter| and |partition| to arbitrary labelled
structures, as described in \pref{sec:programming}.

\subsection{Cartesian product}
\label{sec:cartesian-product}

As we saw earlier, the definition of the standard product operation on
species partitioned the set of labels between the two subshapes.
However, there is nothing to stop us from defining a different
product-like operation, known as \term{Cartesian product}, which does
not partition the labels:\[ (F \scprod G)\ L = F\ L \times G\ L \]
This is the ``na\"ive'' version of product that one might initially
expect.  However, Cartesian product works very differently with
labelled shapes. It is important to remember that a mapping $\Store L
A$ still only assigns a single $A$ value to each label; but labels can
occur twice (or more) in an $(F \times G)$-shape.  This lets us
\emph{explicitly} model value-level sharing, that is, multiple parts
of the same shape can all ``point to'' the same data.  In pure
functional languages such as Haskell or Agda, sharing is a (mostly)
unobservable operational detail; with a labelled structure we can
directly model and observe it. \pref{fig:tree-list-cp} illustrates the
Cartesian product of a binary tree and a list.
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
  \label{fig:tree-list-cp}
\end{figure}

To introduce a Cartesian product shape, one simply pairs two shapes on
the same set of labels.  Introducing a Cartesian product structure is
more interesting. One way to do it is to overlay an additional shape
on top of an existing structure: \[ \cons{cprodL} : F\ L \to \LStr G L A
\to \LStr {F \scprod G} L A. \] There is also a corresponding
$\cons{cprodR}$ which combines an $F$-structure and a $G$-shape.

$(\scprod, \E)$ forms a commutative monoid up to species isomorphism;
superimposing an $\E$-shape has no effect, since the $\E$-shape
imposes no additional structure.

\subsection{Other operations}
\label{sec:other-ops}

\todo{Some introduction here}

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
&\OfSize\ F\ n\ L \defn (\Fin n \iso L) \times F\ L
\end{align*}
The introduction form for $\OfSize$ is simple enough, allowing one to
observe that an existing label type has the size that it has:
\[ \cons{sized} : \Finite L \to \LStr F L A \to \LStr {\OfSize\ F\
  ||L||} L A. \]

% We could also generalize to arbitrary predicates on natural numbers,
% as in
% \begin{align*}
% &\OfSize' : \Species \to (\N \to \Type) \to \Species \\
% &\OfSize'\ F\ P = \lam{L}{(m : \N) \times P\ m \times (\Fin m \iso L)
%   \times F\ L}
% \end{align*}
% The original $\OfSize$ can be recovered by setting $P\ m \defn (m =
% n)$.  However, $\OfSize'$ is difficult to compute with, since $P$ is
% an opaque function.  In practice, $P\ m \defn (m \leq n)$ and $P\ m
% \defn (m \geq n)$ (along with equality) cover the vast majority of
% cases we care about, so as a practical tradeoff we can add explicit
% combinators $\cons{OfSizeLTE}$ and $\cons{OfSizeGTE}$ representing these
% predicates, with parallel introduction forms:
% \begin{align*}
%   \OfSizeLTE\ F\ n\ L &= (L \subseteq \Fin n) \times F\ L \\
%   \OfSizeGTE\ F\ n\ L &= (L \supseteq \Fin n) \times F\ L
% \end{align*}

\paragraph{Derivative and pointing}

The \term{derivative} is a well-known operation on shapes in the
functional programming community~\citep{Huet_zipper,
  mcbride:derivative, abbott_deriv, regular_tree_types,
  mcbride_clowns_2008}, and it works in exactly the way one expects on
species.  That is, $F'$-shapes consist of $F$-shapes with one
distinguished location (a ``hole'') that contains no data
(\pref{fig:derivative}).
  \begin{figure}
    \centering
    \begin{diagram}[width=250]
import SpeciesDiagrams

theDia
  = hcat' (with & sep .~ 1)
    [ struct 5 "F'"
    , text' 1 "="
    , nd (text' 1 "F")
      ( replicate 2 (lf $ Leaf Nothing)
        ++
        [ lf'
            (\p q -> (p ~~ q) # holeStyle)
            (Leaf (Just (circle (labR/2) # holeStyle # fc white # withEnvelope (mempty :: Envelope R2))))
        ]
        ++
        replicate 3 (lf $ Leaf Nothing)
      )
      # drawSpT
    ]

holeStyle = dashing [0.05,0.05] 0

dia = theDia # centerXY # pad 1.1
    \end{diagram}
    \caption{Species differentiation}
    \label{fig:derivative}
  \end{figure}
Formally, we may define
\[ F'\ L \defn (L' : \Type) \times (\under{L'} \iso \TyOne + \under{L}) \times F\ L' \]
Note that a mapping $\Store L A$ associates data to every label
in the underlying $F\ L'$ structure but one, since $\under{L'} \iso \TyOne +
\under{L}$.

To introduce a derivative structure, we require an input structure
whose label type is already in the form $\TyOne + L$:
\begin{align*}
  \cons{d} &: (\under{L'} \iso \TyOne + \under{L}) \to F\ L' \to F'\ L \\
  \lab{\cons{d}} &: (\under{L'} \iso \TyOne + \under{L}) \to \LStr F {L'} A \to A \times \LStr {F'} L A
\end{align*}
The idea behind $\lab{\cons{d}}$ is that we get back the $A$ that used
to be labelled by $\TyOne$, paired with a derivative structure with
that value missing.

A related operation is that of \term{pointing}.  A pointed $F$-shape
is an $F$-shape with a particular label distinguished.  Formally,
\[ \pt{F}\ L \defn L \times F\ L. \]
Introducing a pointed structure simply requires specifying which label
should be pointed:
\begin{align*}
\cons{p} &: L \to F\ L \to \pt{F}\ L \\
\lab{\cons{p}} &: L \to \LStr F L A \to \LStr{\pt{F}} L A
\end{align*}

The relationship bewteen pointing and derivative is given by the
equivalence \[ \pt F \iso \X \sprod F'. \] The right-to-left direction
is straightforward to implement, requiring only some relabelling.  The
left-to-right direction, on the other hand, requires modelling an
analogue of ``subtraction'' on types: the given label type $L$ must be
decomposed as ``$(L - l) + l$'' for some $l : L$, that is, \[ L \iso
\left(\sum_{l':L} l' \neq l \right) + \left(\sum_{l':L} l' = l
\right). \]

\paragraph{Functorial composition}

It is worth mentioning the operation of \emph{functorial composition},
which set-theoretically is defined as the ``na\"ive'' composition

\[ (F \fcomp G)\ L \defn F\ (G\ L). \]

Just as with Cartesian product, functorial composition allows encoding
structures with sharing---for example, the species of simple,
undirected graphs can be specified as \[ \mathcal{G} \defn (\E \sprod \E)
\fcomp (\X^2 \sprod \E), \] describing a graph as a subset ($\E \sprod
\E$) of all ($\fcomp$) ordered pairs chosen from the complete set of
vertex labels ($\X^2 \sprod \E$).

However, functorial composition mixes up labels and shapes in the most
peculiar way---and while this is perfectly workable in an untyped,
set-theoretic setting, we do not yet know how to interpret it in a
typed, constructive way.

\section{Programming with Labelled Structures}
\label{sec:programming}

\todo{bit more intro here?}

There are a number of standard functions on vectors, lists, sets and
bags, finite maps, and similar structures, which we can generalize once
and for all for all labelled structures.

For example, we can implement a |partition| function using the species
$\Part$ of partitions (\pref{sec:sets}) and Cartesian product
(\pref{sec:cartesian-product}). The idea is to usea predicate on data
to divide the labels into disjoint sets.  We then \emph{superimpose}
(via Cartesian product) a second structure on the old, recording this
new information about the labels, without changing the data in any way.
\begin{align*}
&|partition| : \LStr F L A \to (A \to 2) \to \LStr{F \scprod \Part} L
A \\
&|partition|\ (f, |elts|)\ p \defn ((f, |part|), |elts|)\\
& \quad \mathbf{where} \\
& \quad\quad |part| \defn \unit \sprod_e \unit \\
& \quad\quad |e| : \left( \sum_{l : \under L} p\ (|elts ! l|) =
  \cons{True} \right) + \left( \sum_{l : \under L} p\ (|elts ! l|) =
  \cons{False}\right) \iso \under L
\end{align*}
In the end, the superimposed $\Part$ structure contains nothing but an
equivalence showing how the original labels map into a disjoint union
indicating the results of the predicate.

Of course, if we want to actually take this information and ``extract'' the
result (in the usual meaning of splitting the structure into two
distinct pieces), we need to provide a means to do this.

We can extract \emph{both} parts into lists, by pulling apart the
Cartesian Product, then using a (generalized) eliminator over the $\List$
structure (to get the ordering) but using the information from the
``partition'' to make our choices of where to put each element.  Note how the
elements themselves take no part in this choice, but the isomorphism which
is part of the product plays a key role.
\begin{code}
extractBoth :: (S.LabelledStorage s, Set.Enumerable l, Eq l) =>
    Sp (L.L # Part) s l a -> ([a], [a])
extractBoth sp =
  let (lsp, part) = decompL sp
  in gelim (L.gelimList ([],[])
      (\(l,a) (ll,rl) ->
        case part of
          Prod _ _ eiso ->
            case view (from eiso) l of
              Left _  -> (a:ll,rl)
              Right _ -> (ll,a:rl))) lsp
\end{code}

To actually implement the Prelude partition, we have to specialize the
above two functions to work over a $\List$, using a specific label set and
mapping \footnote{LFA stands for 'list-fin-arrow'}.
\begin{code}
partitionLFA :: N.Natural n => Sp L.L (->) (F.Fin n) a -> (a -> Bool) -> Sp (L.L # Part) (->) (F.Fin n) a
partitionLFA = partition

extractBothLFA :: N.Natural n => Sp (L.L # Part) (->) (F.Fin n) a -> ([a],[a])
extractBothLFA = extractBoth
\end{code}

Putting all these pieces together (along with some standard routines for dealing
with length-indexed vectors), we reimplement the Prelude's $|partition|$:
\begin{code}
partition' :: (a -> Bool) -> [a] -> ([a],[a])
partition' p lst = case Vec.fromList lst of
  Vec.SomeVec v ->
      N.natty (Vec.size v) $ extractBothLFA $ partitionLFA (fromVec v) p
\end{code}

Using very similar techniques (\cons{partition} stays the same, only
\cons{extract} needs to change), we can easily implement \cons{filter},
\cons{elem} and \cons{find}.  With a bit more work, \cons{findIndex} and
\cons{elemIndex} as well\footnote{We use the names from \cons{Data.Vector}}.
We can implement more complex routines too, such as \cons{findIndices}:
\begin{code}
findIndices :: (S.Storage s, Set.Enumerable l, Eq l) =>
          Sp f s l a -> (a -> Bool) -> E l
findIndices sp p = elim k (Struct gl es)
  where sp' = partition sp p
        Struct (CProd _ gl) es = sp'
        k = elimProd $ \pf -> elimE $ \s -> elimE $ const
               (E $ Set.injectionMap (\(l,_) -> view pf (Left l)) s)
\end{code}
Again, $|partition|$ is important, but the labels are key.  It is important
to remember that all algebraic data types are labelled structures: when
we add labels, we add ``addresses'' to each datum in a structure, which can
be used to retrieve them at a later point.  In other words, our
\emph{abstract labels} play the role traditionally taken by \emph{pointers}
in low-level languages.

Other functions which traditionally rely on $|Traversable|$ can be
implemented straightforwardly.  We give $|all|$ as an example:
\begin{code}
all :: (S.Storage s, Set.Enumerable l, Eq l) => Sp f s l a -> (a -> Bool) -> Bool
all sp p = elim k (Struct gl es)
  where sp' = partition sp p
        Struct (CProd _ gl) es = sp'
        k = elimProd (const $ elimE (const $ elimE Set.isEmpty))
\end{code}
The above relies on the property that $|all|$ is equivalent to having
the $|snd|$ set of a partition be empty -- something that can be coded up
directly.

The definition of the $|product|$ of two labelled structures may not make this
entirely transparent, but it allows us to implement \emph{concatenation}.
Just as \cons{partition} is the heart of many of the routines described
above, \cons{product} corresponds to concatenation of lists, concatenation
of vectors, union of finite maps, union of bags, and so on. \jc{code
omitted, see \cons{lcat} in VecLike}.

\paragraph{Foldable}  Since we can extract a list from
an arbitrary \cons{Foldable} functor, we can just as easily get an
(implicitly) labelled $L$-structure from \cons{Foldable}.  In the opposite
direction, we can also get \cons{Foldable} from the presence of an
$L$-structure; more explicitly:
\begin{code}
instance F.Foldable (Sp' (f # L) s) where
  foldr f b (SpEx (Struct (CProd _ f2) elts)) = elim (elimList b f) (Struct f2 elts)
\end{code}
\noindent This strongly indicates that \cons{Foldable} is really about
\emph{order}: it does not matter what $f$-structure we have, as long as we
have a superimposed linear order on the labels \emph{without the labels
themselves being ordered}, we have enough information for ``folding''.

Following this idea, we can use this to implement many useful functions
such as \cons{sum}, \cons{product}, \cons{and}, \cons{or} over arbitrary
labelled structures.
\begin{code}
product :: (S.Storage s, Set.Enumerable l, Eq l) => Sp f s l Int -> Int
product sp = elim k (forgetShape sp)
  where k = elimE $ \s -> Data.MultiSet.fold (*) 0 $ Set.smap snd s
\end{code}

While the above is perfectly correct, Haskell is also perfectly happy with
\begin{code}
instance (Set.Enumerable l, Eq l, S.Storage s) => F.Foldable (Sp f s l) where
  foldr g b sp = elim k (forgetShape sp)
    where k = elimE $ \s -> MS.fold g b $ Set.smap snd s
\end{code}
\noindent we are not.  It basically says that all labelled structures are
\cons{Foldable}, which we do not want.  The error in the above is that
\cons{MS.fold} \emph{says} that it works for an arbitrary order of the
underlying elements, but this is not checked.  Worse, by using a
non-associative function $|f|$, we can actually \emph{observe} the order that
was used, something we should most definitely not be able to do.  To be
correct, the above should \emph{restrict} $|g|$ to be an
\emph{associative, commutative} function, but alas, this cannot be done
in Haskell.  The ``fault'', such as it is, really lies in the
$|Data.MultiSet|$ package exposing a much too general notion of \cons{fold}.

\paragraph{Lens}
The labels allow even more: we can create a \emph{lens} for any labelled
structure which focuses on an arbitrary label:
\begin{code}
lensSp :: (S.Storage s, S.LabelConstraint s l) => l -> Lens' (Sp f s l a) a
lensSp lbl =
    lens (\(Struct _ e) -> S.index e lbl)
         (\(Struct sh e) a -> Struct sh (snd $ S.replace lbl a e))
\end{code}
\noindent The vast majority of the instances of \cons{Lens} are simply
specializations of the code above for specific structures.

It should be pointed out that an even more idiomatic implementation of
\cons{lensSp} would first \emph{point} the $f$-structure, and then using
that as its focus, derive a lens for it.

\paragraph{take} \jc{Not sure about this one.}  If we also fix the type
of labels such that they are canonically ordered, other functions can also
be implemented generically, such as \cons{take}.
\begin{code}
take :: forall f a q n s.
  Sp f s (F.Fin q) a -> N.SNat q -> N.SNat n -> (n <= q)
     -> Sp (f # Part) s (F.Fin q) a
take (Struct f i) qq n pf =
  case minus qq n pf of
    Minus (m :: N.SNat m) Refl ->
      case N.plusComm m n of
        Refl -> Struct (cprod_ f (part_ sn sm isom)) i
          where isom :: Either (F.Fin n) (F.Fin m) <-> F.Fin q
                isom = iso (finSum n m) (finSum' n m)
                sn = N.natty n $ Set.enumerate finite_Fin
                sm = N.natty m $ Set.enumerate finite_Fin
\end{code}
This is much more involved.  It requires quite a lot of data: an $f$-structure
labelled with natural numbers with $q$ labels, a witness for $q$, a witness
for $n$ (the number of data we want to ``take''), and a proof that this is less
than $q$, \ie\ that there is indeed enough data to fulfill this request.
We again superimpose a \cons{Part} structure onto the $f$-structure.  The
dependence on the ordering is natural for \cons{take}, but not for
labelled structures.

We can easily imagine a variant of this, where rather than picking the
``first $n$'' labels, we instead choose a specific subset of labels.  This
would be a much more (labelled-structure) idiomatic version of \cons{take}.

\section{Vector mappings}
\label{sec:vecmap}

Section~\ref{sec:mappings} introduced the requirements that a mapping 
$\Store - -$ from labels to data must satisfy, and showed that functions
can be used as mappings.  But such an implementation is somewhat 
degenerate, in that it does not use the information that label sets
are finite.  The isomorphisms given in |reindex|, |append| and
|concat| are used, but in a fairly superficial manner.

Our goal here is to show that we can model low-level concerns such
as memory layout, allocation and manipulation, in a uniform manner for
all labelled structures.  To model a consecutive block of memory, 
we will implement a mapping using finite vectors to store the $A$ values. 
More precisely, we use length-indexed vectors; this gives a very detailed view
of the memory layout, allocation and manipulation required for storing the data
associated with labelled structures.  As we will see, for such mappings,
\emph{finiteness} is crucial, and the finiteness proofs are
all computationally relevant.

Concretely, we assume a type $|Vec| : \N \to \Type \to
\Type$ of length-indexed vectors, supporting operations
\begin{align*}
  |allocateV| &: (n : \N) \to (\Fin n \to A) \to \Vect n A \\
  |(!)|       &: \Vect n A \to \Fin n \to A \\
  |mapV|      &: (A \to B) \to (\Vect n A \to \Vect n B) \\
  |foldV|     &: R \to (R \to A \to R) \to \Vect n A \to R \\
  |appendV|   &: \Vect m A \to \Vect n A \to \Vect {(m + n)} A \times
  (\Fin m + \Fin n \iso \Fin{(m + n)}) \\
  |concatV|   &: \Vect m {(\Vect n A)} \to \Vect {(m \cdot n)} A \times
  (\Fin m \times \Fin n \iso \Fin (m \cdot n))
  % |sumV|      &: (|ns| : \Vect m \N) \to |mapV (\n -> Vec n A) ns| \\
  % &\qquad \to \Vect {(|sumN ns|)} A \times
  % (|sumTy|\ (|mapV|\ \Fin{}\ |ns|) \iso \Fin (|sumN ns|))
%  imapV     &: (\Fin n \to A \to B) \to (\Vect n A \to \Vect n B) \\
%  zipWithV  &: (A \to B \to C) \to \Vect n A \to \Vect n B \to \Vect n C
\end{align*}
Note that in addition to computing new vectors, |appendV| and
|concatV| also yield equivalences which encode the precise
relationship bewteen the indices of the input and output vectors.  For
example, if |appendV v1 v2 = (v,e)|, then it must be the case that |v1
! m = v !  (e (inl m))|.  Similarly, |v ! m ! n = v' ! (e (m,n))| when
|concatV v = (v',e)|.

% |sumV| is a generalized version of |concatV|
% allowing the concatenation of a collection of vectors of varying
% length,
% \begin{equation*}
%   \begin{minipage}[c]{200pt}
%   \hfill
%   \begin{diagram}[height=15]
%     dia = pad 1.1 . centerXY
%         . hcat' (with & sep .~ 0.5) . map (hcat . flip replicate (square 1))
%         $ [ 4, 2, 5 ]
%   \end{diagram}
%   %$
%   \end{minipage}
%   \stackrel{|sumV|}{\longrightarrow}
%   \begin{minipage}[c]{200pt}
%   \begin{diagram}[height=15]
%     dia = pad 1.1 . centerXY
%         . hcat . flip replicate (square 1) . sum
%         $ [ 4, 2, 5 ]
%   \end{diagram}
%   %$
%   \end{minipage}
% \end{equation*}
% with |sumN = foldV 0 (+)| and |sumTy = foldV undefined (+)|.

Given such a type $\cons{Vec}$, we may define \[ \Store L A \defn \sum_{n :
  \N} (\under L \iso \Fin n) \times \Vect n A, \] and implement the required
operations as follows:

\begin{itemize}
\item The implementation of |allocate| uses the (implicitly provided)
  proof $(n, iso) : \Finite {\under L}$ to determine the size of the
  vector to be allocated, as well as the initial layout of the values.
  \begin{spec}
    allocate {n,iso} f = (n, inv(iso), allocateV n (f . iso))
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
  not coincide with zipping on indices. Since we want to zip on
  indices, |zipWith| must compose the given equivalences to obtain the
  correspondence between the label mappings used by the two input
  vectors:
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
    append e (n1, i1, v1) (n2, i2, v2) = (n1+n2, e . (i1 + i2) . f, v)
      where (v,f) = appendV v1 v2
  \end{spec}
  Note that we construct the required label equivalence as the
  composite \[ \under L \stackrel{e}{\iso} \under{L_1} + \under{L_2}
  \stackrel{i_1 + i_2}{\iso} \Fin{n_1} + \Fin{n_2} \stackrel{f}{\iso}
  \Fin{(n_1 + n_2)}, \] using the provided equivalence |e| and the
  index equivalence |f| returned by |appendV|.

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
this, in exchange for some bookkeeping overhead, we could make a deep
embedding out of the vector operations, turning |appendV| and
|concatV| (and possibly |allocateV| and |mapV| as well) into
\emph{constructors} in a new data type.  This results in something
that looks very much like generalized tries
\cite{Hinze-generalized-tries}.

\section{Labelled Structures in Haskell}
\label{sec:haskell}

\todo{
  Interesting points of our implementation in Haskell.
  \begin{itemize}
  \item Link to (public) git repo
  \item Heavy use of DataKinds etc. to simulate dep types (cite Hasochism)
  \item Needs to use existentially quantified labels in place of
    dependency, e.g. for $\compB$.  And for products.
  \item Uses the lens lib for isos and subset.
  \item A lot of overhead; actually compiling such things to efficient
    runtime code is future work.
  \end{itemize}
}

\subsection{Labelled eliminators}
\label{sec:labelled-eliminators}

\todo{overhaul this section.  Most of it is irrelevant/wrong now.
  Just put as much as we need to be able to use eliminators in our
  examples.}

\bay{With our old-style eliminators (i.e. the ones which were required
  to work for all label types), we had to sort of CPS-encode them to
  make it work.  Building up an eliminator using the combinators like
  |elimE|, |elimProd|, etc. corresponds to writing a CPS-encoded
  computation.  It occurred to me the other day, though, that with our
  ``generalized'' eliminators, which can look at the labels, this is
  unnecessary.  We can just directly pattern-match on labelled
  structures.  So I think we should downplay the whole eliminator
  thing and just write our examples in a direct style.}

% Depending on the representation used for the map type $\Store L A$, a
% given labelled structure can have multiple distinct
% representations. Ideally, this extra representation detail should be
% unobservable when writing programs using labelled structures (although they
% will likely have an effect on resource usage). In addition,
% species, and hence labelled structures, are functorial in the label
% type, so the precise nature of the labels should not be observable
% either---that is, computing some function of a labelled structure
% should give the same result if we first relabel it.  We can accomplish
% this by making the type of labelled structures abstract, and carefully
% defining a type of \emph{eliminators} for labelled structures which
% hide the extra detail.

% \bay{Argh, it just hit me that this story about getting the same
%   result before and after relabelling is inconsistent with our story
%   about operations on arrays as label operations.  There is something
%   more subtle going on here but I am not sure what.}
% \jc{That is because species based on $\B$ alone cannot model arrays.
% This is why you need more 'visible' structure on the label set to be
% able to do anything except relabelling.  Another approach is to move
% the structure to the shape component -- which we can't do in time for this
% paper.}

% \jc{The `problem' with this definition is that it does not fully
% correspond to the Haskell implementation.  In particular, we don't really
% have access to (the type) L from within the eliminator.  And the most
% interesting examples require a slight generalization.}
% The generic type of eliminators for labelled $F$-structures, $\Elim_F
% : \Type \to \Type \to \Type$, is defined by
% \begin{equation*}
%   \Elim_F\ A\ R \defn (L : \Type) \to F\ L \to \DecEq L \to \Store L A \to R
% \end{equation*}
% where $\DecEq L$ represents decidable equality for $L$. There are a
% few subtle issues here which are worth spelling out in detail. First,
% note that $\Elim_F$ is parameterized by $A$ (the type of data elements
% stored in the labelled structure being eliminated) and $R$ (the type
% of the desired result), but \emph{not} by $L$.  Rather, an eliminator
% of type $\Elim_F\ A\ R$ must be parametric in $L$; defining an
% eliminator which works only for certain label types is not allowed.
% The second point is that we assume that $\Store L A$ is held abstract;
% an eliminator cannot make use of any details of a particular
% implementation for $\Store L A$, but only its abstract interface (in
% particular, the |index| function).

% Decidable equality on $L$ allows the eliminator to observe value-level
% sharing.  If $\DecEq L$ is left out, we have \[ (L : \Type) \to F\ L
% \to \Store L A \to R, \] which by parametricity is equivalent to \[ F\
% A \to R. \] That is, if we do not observe the sharing (\ie\ if we do not
% consult the decidable equality on $L$, to see which labels occur more
% than once), then semantically speaking we might as well simply replace
% the labels in the $F$-shape with their corresponding $A$ values, and
% then eliminate that. However, from an operational point of view, even
% without any sharing, filling in the $F$-shape with data might involve
% undesirable copying of large amounts of data.

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

% We can always derive decidable equality for any type with a $\Finite$
% proof, by mapping to $\Fin n$ and comparing for equality.  However, we
% do not expose the actual $\Finite L$ witness to eliminators.  The
% reason is that given a value of $\Finite L$, one can observe an
% induced linear order on the elements of $L$, using the usual linear
% order on the associated natural numbers. However, this would again
% break functoriality: an eliminator would be able to observe some of
% the effects of relabelling. Given only $\DecEq L \times (L \to A)$,
% there is no way to enumerate the elements of $L$ or observe any order
% relation on them.  One can only traverse the shape $F\ L$ and feed
% encountered $L$ values into the $(L \to A)$ function to learn the
% associated data values, possibly consulting the provided decidable
% equality to find out which labels are shared.

% Note that if we do want to observe sharing, the given formulation is
% not actually very convenient; for example, if we want to know whether
% a given label $l : L$ is shared, we have to traverse the entire
% $F$-structure and test every label for equality with $l$.  In
% practice, there may be equivalent, more operationally convenient
% formulations.

% We can ``run'' an eliminator,
% \[ \elim : \Elim_F\ A\ R \to \LStr F L A \to R, \] by taking apart the
% labelled structure and using it to construct the proper arguments to
% the eliminator.

% \todo{mention in this section that this doesn't give you any help in
%   eliminating $F\ L$, which for some species $F$ may be nontrivial
%   (\eg anything with symmetry).  Future work.}

\section{Related work}
\label{sec:related}

The work on \emph{containers}
\citep{abbott_categories_2003,abbott_deriv,abbott_quotient,alti:cont-tcs,alti:lics09}
also aims to find a more general theory of data structures which
captures a large set of ``containers''.  The resulting theory is quite
elegant.  It involves \emph{shapes} and a family of \emph{position}
types indexed by shapes.  More formally, it is a dependent pair of
types $A : \Type$ and $B : A \to \Type$ (which they write $A\lhd B$) which
yields a functor $T_{A\lhd B} X$ defined as $\Sigma a:A. X^{B\left(a\right)}$.
Roughly, their positions correspond to our labels, their shapes
correspond to our labelled shapes, and the associated functor maps
positions to data values, much as our mappings associate data values
to labels.  They have developed the theory quite far; as of yet,
however, there is no implementation of containers, nor is there a
fully developed dictionary linking concrete structures to the
corresponding abstract container.  It is thus difficult to do a deeper
comparison of the approaches.  We can nevertheless make a few simple
observations.  One significant difference is that in the containers
work, each shape is associated with a fixed, inherent set of
positions, whereas in our approach a shape can be used with any type
of labels.  Furthermore, for them shape is an input, while for us it
is part of what is generated.  As a result, with containers, it does
not seem that the positions can easily be given extra structure (the
work on quotient containers~\citep{abbott_quotient} is quite
involved).  There are fewer combinators for containers than for
labelled structures: for example, neither the Cartesian product nor
functorial composition seem to be present.  Thus there is as of yet no
theory of sharing for containers, nor is there a fine grained theory of
storage.  Having said all of that, however, containers are not restricted to
finite sets of labels, which makes them more general than labelled structures: there
are useful types (such as streams) which are containers but not labelled
structures.  And therein seems to be the main difference: the extra
generality allows containers to encapsulate fancier types, while our
concreteness lets us uniformly and easily model low-level concerns.

Shapely types \citep{jay-shapely} are closely related to containers---
see~\citet[section 8]{abbott_categories_2003} for a careful
explanation of the details.  Their results show that shapely types are
those containers which are closest to labelled structures: in many
settings of importance, shapely types are \emph{discretely finite}
containers, which essentially amounts to saying that all shapes give
rise to a finite number of positions (\ie labels).  Shapely types do
not explicitly make use of labels at all, but since they involve
\emph{lists} of data values, one may say that they implicitly make
use of labels from $\Fin n$.  There is thus a close relationship to
our constructive finiteness proofs for label types.  Furthermore,
there are claims \citep{jay-shapely} that this also corresponds to
information about memory allocation and layout, however this is not
detailed anywhere in the literature.

Another approach is that of \textit{Container Types Categorically}
\citep{ContainerTypesCat}.  They define containers as monotone
endofunctors $F$ on \cons{Rel} (\ie \emph{relators}) which have a
\emph{membership relation}; this latter concept turns out to be a special
kind of lax natural transformation from $F$ to the identity functor.
This approach is again rather difficult to adequately compare to ours.
There is again overlap, but no inclusion in either direction.

From the categorical perspective, \emph{stuff types}
\citep{BaezDolan01,Morton2006}, brilliantly explained in Byrne's
master's thesis \citeyearpar{Byrne2005}, are directly related to
species.  Stuff types are functors from some arbitrary groupoid $X$ to
the groupoid of finite sets and bijections.  Faithful stuff types are
equivalent to species.  But these work much like containers: stuff
types map a structure to its underlying set (which can be thought of as
positions), instead of mapping labels to structures.  In a different
direction, \emph{polynomial functors} also generalize
species~\citep{kock2012data}, and seem a categorically solid
foundation for an even more general approach to data type
constructors.  Unfortunately, no one has yet to unravel these
definitions into something suitable for implementation.  Similarly,
\emph{generalised species of structures}~\citep{Fiore08} may also be
another interesting direction.  But in all these cases, there remains
much work to be done to bridge theory and practice.

Species have been the basis for many implementations in the area of
enumerative combinatorics, such as Darwin~\citep{Berg85},
\LUO~\citep{FlajoletSalvyZimmermann1989a}, combstruct~\citep{FlSa95},
Aldor-Combinat~\citep{Aldor-Combinat} and
MuPAD-Combinat~\citep{Mupad-Combinat}.  Most do not model the full
spectrum of species combinators, but make up for it by implementing
very sophisticated algorithms for enumeration and generation, both
exhaustive and random.  The Haskell species package
\citep{yorgey-2010-species, species} is a fairly direct implementation
of the theory of species, without attempting to use this theory as a
foundation for data structures.

Lastly, we should note that we have used but a small fraction of the
theory of species.  \citet{bll} alone still contains a vast trove of
further examples (sometimes buried deep in the exercises!) of
relevance to programming.  We have also not yet really touched the
\emph{calculus} aspects of the theory; while the derivative is by now
well-known, integration~\citep{Rajan93} has not really been explored.
There are also new variants on
species~\citep{Schmitt93hopfalgebras,Menni2008,Maia2008arithmetic,aguiar2010monoidal}
with nontrivial applications to combinatorics, and possible
applications to programming as well. Species have even been applied to
the study of attribute grammars~\citep{Mishna03b}.

\section{Future work}
\label{sec:future}

We have only started our translation of the theory of species to
constructive type theory.  But already many different threads of 
work are clear to us.

\paragraph{Capture more of the extant theory.}  Several of the 
species operations (such as pointing, functorial composition and arithmetic
product) seem quite powerful, but we have yet to leverage them properly.
Similarly, we have made very little use of \term{symmetry} beyond the
extreme cases (ADTs have none, and $\E$ has all symmetries).  For example,
a \term{cycle} is like a list, except
that it is invariant under cyclic rotation of its labels.  One area
where cycles are especially useful is in computational geometry: we
can represent an (oriented) polygon, for example, as a labelled cycle
shape, with each label mapping to a point in space.
%\todo{picture of a polygon represented with labelled cycle}

We have also not yet pursued weighted species, multisorted species, nor
virtual species, all of which look quite promising for applications.
We can also investigate other categories of labels:  for example,
  $\mathbb{L}$-species \citep{Joyal86}, \citep[chap. 5]{bll} use
  linearly ordered labels; the link with Girard's normal functors
  \citep{Girard1988} is also worth pursuing in more detail.
  We firmly believe that alternate categories of labels will have
  significant benefits in a computational setting.

It is worth noting that much of the power of the theory of
species---at least in the context of combinatorics---can be traced to
fruitful homomorphisms between algebraic descriptions of species and
rings of formal power series.  How much of this is constructive, and
how much is computationally relevant?

Another route of investigation are \emph{tensorial species}
\citep[chap. 4]{Joyal86}, which are functors to $\cons{Vect}$ rather
than $\Set$.  These seem to be directly related to our vector mappings
(section~\ref{sec:vecmap}).  

Lastly, there are several powerful theorems (like the molecular
decomposition and the implicit species theorem) that we have yet to
leverage.  In the case of (small) finitary species, the molecular 
decomposition theorem could be used as a powerful means to specialize
complex species code down to much simpler operations on a few well
understood cases.

\paragraph{Memory allocation}  One of the most intriguing aspects of
this elaboration of labelled structures are the close links with
memory allocation and layout.  This could lead to a uniform mechanism
for \emph{unboxing} of algebraic data types, at least when their size
is statically known (or even statically known to be bounded and small).
We feel like we have just scratched the surface of this link.  Combined
with an appropriate theory of structured labels (to handle 
multi-dimensional arrays in a principled manner), we hope to be able
to give a more uniform explanation for various memory layout strategies
commonly used in high-performance linear algebra computations.

Along with this, there is a particular labelled structure, \emph{subset},
which is particularly interesting.  Combinatorially, it is equivalent to
a partition, \ie\ $\E \sprod \E$.  However, semantically a subset 
corresponds to only the \emph{left} component of that product, and the right 
component should be ignored.  In other words, we can use subset to indicate
that only a subset of labels need be stored.

\paragraph{Categorical requirements}

As is clear from the species literature, there are quite a number of 
useful variations in the exact categories used for species.  We have 
not been able to find a systematic treatment giving minimal assumptions
required for the validity of the various constructions (sum, product, cartesian
product, etc).  We plan to pursue this quite formally, by first porting
our implementation to Agda, as a means to prove the various properties.

In particular, outside of combinatorial uses, it is unclear exactly 
where \emph{finiteness} is crucial.

\paragraph{HoTT and reversible programming}

The links with homotopy type theory run deeper than what we have used
here, and deserved to be explored.  For example, lists as ADTs are 
unique (for each size), whereas here there are many lists as labelled
structures (for each size), although all of them are \emph{equivalent}.
This joins up nicely with HoTT, which teaches us to use equivalences 
rather than quotients.  The groupoid of equivalences of labels is 
related to the identity type of the label set -- though details obviously
need to be worked out.

Another link is with reversible programming, and more particularly with
the language $\Pi$ of \citep{InformationEffects}.  While we use
arbitrary isomorphisms between finite sets, $\Pi$ is a convenient
\emph{language} in which to write (and reason about) those isomorphisms.


\section{Conclusion}
\label{sec:conclusion}

\bibliographystyle{plainnat}
\bibliography{SpeciesAsConstructors}

\end{document}
