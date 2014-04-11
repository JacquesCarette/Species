%% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass{entcs}

\usepackage{prentcsmacro}

\providecommand{\event}{MSFP 2014}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include lhs2TeX.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
% \arrayhs

% \renewcommand{\Conid}[1]{\mathsf{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Package imports

%\usepackage{amsthm} %% conflicts with entcsmacro
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{stmaryrd}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}
\usepackage[all]{xy}
\usepackage{breakurl}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Diagrams

\usepackage{graphicx}
\usepackage[outputdir=diagrams,backend=cairo,extension=pdf]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{\Sect\ref{#1}}
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

%\newif\ifcomments\commentstrue
\newif\ifcomments\commentsfalse

\ifcomments
\newcommand{\authornote}[3]{\textcolor{#1}{[#3 ---#2]}}
\newcommand{\todo}[1]{\textcolor{red}{[TODO: #1]}}
\newcommand{\chaptertodo}[1]{\textcolor{gray}{[TODO (Later): #1]}}
\else
\newcommand{\authornote}[3]{}
\newcommand{\todo}[1]{}
\newcommand{\chaptertodo}[1]{}
\fi

\newcommand{\bay}[1]{\authornote{blue}{BAY}{#1}}
\newcommand{\jc}[1]{\authornote{purple}{JC}{#1}}
\newcommand{\scw}[1]{\authornote{magenta}{SCW}{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Semantic markup

\newcommand{\eg}{\latin{e.g.}\xspace}
\newcommand{\ie}{\latin{i.e.}\xspace}
\newcommand{\etal}{\latin{et al.}\xspace}
\newcommand{\etc}{\latin{etc.}\xspace}

\newcommand{\term}[1]{\emph{#1}}
\newcommand{\latin}[1]{\textit{#1}}
\newcommand{\foreign}[1]{\emph{#1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Misc

\newcommand{\LUO}{$\Lambda$\kern -.1667em\lower .5ex\hbox{$\Upsilon$}\kern -.05em\raise .3ex\hbox{$\Omega$}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Math typesetting

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% General math

\newcommand{\bbb}[1]{\ensuremath{\mathbb{#1}}}
\providecommand{\N}{\bbb{N}}
\providecommand{\Z}{\bbb{Z}}
\providecommand{\Q}{\bbb{Q}}
\providecommand{\R}{\bbb{R}}
\providecommand{\C}{\bbb{C}}

\newcommand{\mcal}[1]{\ensuremath{\mathcal{#1}}}
\let\Sect\S
\renewcommand{\S}{\mcal S}
\renewcommand{\H}{\mcal H}
\newcommand{\I}{\mcal I}
\newcommand{\Sym}{\mcal S}

\newcommand{\msf}[1]{\ensuremath{\mathsf{#1}}\xspace}

\newcommand{\param}{\mathord{-}}

\newcommand{\comp}{\mathbin{\circ}}
\newcommand{\union}{\cup}
\newcommand{\Union}{\bigcup}
\newcommand{\intersect}{\cap}
\newcommand{\Intersect}{\bigcap}

\newcommand{\floor}[1]{\left\lfloor #1 \right\rfloor}
\newcommand{\ceil}[1]{\left\lceil #1 \right\rceil}

\newcommand{\bij}{\stackrel{\sim}{\longrightarrow}}
\newcommand{\iso}{\simeq}
\newcommand{\mkIso}{\rightleftharpoons}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Type theory

\newcommand{\universe}{\mcal{U}}
\newcommand{\defeq}{\mathrel{\vcentcolon\equiv}}
\newcommand{\dep}[1]{\prod_{#1}}
\newcommand{\fun}[1]{\lambda #1.\ }

\newcommand{\TyZero}{\ensuremath{\bot}\xspace}
\newcommand{\TyOne}{\ensuremath{\top}\xspace}
\newcommand{\unit}{\ensuremath{\star}\xspace}

\newcommand{\cons}[1]{\ensuremath{\mathsf{#1}}}

\providecommand{\False}{}
\renewcommand{\False}{\cons{F}}
\providecommand{\True}{}
\renewcommand{\True}{\cons{T}}

\newcommand{\inl}{\cons{inl}}
\newcommand{\inr}{\cons{inr}}
\newcommand{\outl}{\cons{outl}}
\newcommand{\outr}{\cons{outr}}

\newcommand{\Type}{\ensuremath{\mathcal{U}}}
\newcommand{\FinType}{\ensuremath{\Type_{\text{Fin}}}}
\newcommand{\FinTypeT}{\ensuremath{\Type_{\||\text{Fin}\||}}}
\newcommand{\size}[1]{\ensuremath{\##1}}

\newcommand{\Fin}[1]{\ensuremath{\cons{Fin}\ #1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% HoTT

\newcommand{\ptrunc}[1]{\ensuremath{\left\||#1\right\||}}
\newcommand{\id}{\cons{id}}

\newcommand{\tygrpd}[1]{\ensuremath{\mathbf{G}(#1)}}

\newcommand{\transport}[2]{\ensuremath{\mathsf{transport}^{#1}(#2)}}

\newcommand{\ua}{\ensuremath{\mathsf{ua}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Category theory

% typesetting for category names
\newcommand{\cat}[1]{\ensuremath{\mathbf{#1}}\xspace}

\newcommand{\op}{\ensuremath{\mathrm{op}}}            % opposite category
\newcommand{\disc}[1]{\ensuremath{\left||#1\right||}} % discrete category
\newcommand{\then}{\mathbin{;}}                       % flipped composition

% morphisms
\newcommand{\mor}[2]{\ensuremath{#1 \longrightarrow #2}}
\newcommand{\nat}[2]{\ensuremath{#1 \stackrel{\bullet}{\longrightarrow} #2}}

% some standard categories
\newcommand{\Set}{\cat{Set}}

\providecommand{\B}{\bbb{B}}
\renewcommand{\P}{\bbb{P}}
\providecommand{\FinSet}{\bbb{E}}

\newcommand{\BT}{\mcal{B}}
\newcommand{\PT}{\mcal{P}}

\newcommand{\fin}[1]{\ensuremath{[#1]}}

% monoidal lifting
\newcommand{\lifted}[1]{\hat{#1}}
\newcommand{\lotimes}{\mathbin{\lifted{\otimes}}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Species

\renewcommand{\Sp}{\msf}
\newcommand{\X}{\Sp{X}}
\newcommand{\Y}{\Sp{Y}}
\newcommand{\E}{\Sp{E}}
\newcommand{\F}{\Sp{F}}
\newcommand{\G}{\Sp{G}}
\renewcommand{\L}{\Sp{L}}
\newcommand{\T}{\Sp{T}}
\newcommand{\Par}{\Sp{Par}}
\newcommand{\Bag}{\Sp{E}}
\newcommand{\Cyc}{\Sp{C}}

\newcommand{\Zero}{\msf{0}}
\newcommand{\One}{\msf{1}}

\newcommand{\sprod}{\cdot}
\newcommand{\fcomp}{\mathbin{\square}}

\providecommand{\comp}{\circ}

\newcommand{\usum}{\boxplus}
\newcommand{\uprod}{\boxtimes}
\newcommand{\ucomp}{\boxcircle}

\newcommand{\unl}[1]{\widetilde{#1}}

\newcommand{\Lab}{\bbb{L}}
\newcommand{\Str}{\bbb{S}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Haskell

%format `mappend` = "\mappend"
%format mempty = "\mempty"

\newcommand{\mappend}{\diamond}
\newcommand{\mempty}{\varepsilon}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Frontmatter

\def\lastname{Yorgey, Carette, Weirich}

\begin{document}

\begin{frontmatter}
\title{Generalizing species to type theory}

%% ENTCS

\author[Penn]{Brent A. Yorgey},
\author[Mac]{Jacques Carette},
\author[Penn]{Stephanie Weirich}

\address[Penn]{Dept. of Computer and Information Science\\
 The University of Pennsylvania\\
 Philadelphia, Pennsylvania, USA}
\address[Mac]{Dept. of Computing and Software\\ McMaster University\\
 Hamilton, Ontario, Canada}

%\thanks[myemail]{Email:\href{mailto:byorgey@cis.upenn.edu}
%{\texttt{\normalshape byorgey@cis.upenn.edu}}}


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
% \author{
%   Brent A. Yorgey \quad\quad Stephanie Weirich
%   \institute{
%     Dept. of Computer and Information Science\\
%     The University of Pennsylvania\\
%     Philadelphia, Pennsylvania, USA
%   }
%   \and
%   Jacques Carette
%   \institute{
%     Dept. of Computing and Software\\ McMaster University\\
%     Hamilton, Ontario, Canada
%   }
% }
% \def\authorrunning{B. Yorgey, J. Carette, S. Weirich}

\begin{abstract}
  This paper develops a constructive definition of Joyal's theory of
  combinatorial species using Homotopy Type Theory. We justify our definitions
  by generalizing various operations on species to arbitrary functor
  categories. In particular, we use lifted monoids to define species sum and
  cartesian product, and day convolution to define partitional and arithmetic
  products. This foundational work is the first step in the application of the
  theory of species to a wide class of data structures.
\end{abstract}

\begin{keyword}
Combinatorial Species, Homotopy Type Theory
\end{keyword}

\end{frontmatter}

\section{Introduction}
\label{sec:intro}

The theory of \emph{combinatorial species} is was first set forth by
Joyal~\cite{joyal} as a system for understanding and unifying much of
\emph{enumerative combinatorics}, the branch of mathematics concerned with
counting abstract structures. Accordingly, this theory provides a unified view
of structures, presenting them in a general, compositional framework.
Furthermore, there seems to be a connection between this framework of abstract
structures and the data structures that programmers use. We can think of these
structures as some sort of ``shape'' containing \emph{labeled positions} or
\emph{locations}. When paired with a mapping from those labels to actual data,
species models familiar data structures, such as algebraic datatypes. We would
like to use this beautiful theory to enrich and expand our
understanding of computational structures.

However, teasing out the precise relationship between species and data
structures has proved challenging, for two reasons. First, combinatorialists
are mainly concerned with enumerating and generating abstract structures, not
with storing and computing with data.  Thus, in order to apply this theory in
a computational setting, there are hidden assumptions and glossed
distinctions that must first be made explicit.  Second, being situated in
traditional mathematical practice rooted in set theory,
% \footnote{notwithstanding the fact that the foundational work is
%   categorical},
species are described in ways that are \emph{untyped} and
\emph{nonconstructive}, both of which hinder adoption and understanding in a
computational context.

In this paper, we create a bridge between the theory of species and the theory
and practices of programming. In particular, we ``port'' the definitions of
combinatorial species to constructive type theory, making the theory more
directly applicable in a programming context and more accessible to functional
programmers.

This port is nontrivial. In fact it took us several tries to get definitions
that worked adequately. Part of the difficulty lies in the fact that
species are defined over \emph{finite} sets of labels.  In a classical
setting, while finiteness is a crucial part of the definition, it is an
otherwise fairly implicit feature of the actual theory.  Combinatorialists do
not need to remind themselves of this finiteness condition, as it is a
pervasive axiom that you can only ``count'' finite collections of objects.
When ported to a constructive setting, however, the notion of finiteness takes
on nontrivial computational content and significance.  In particular, we are
naturally led to work up to computationally relevant \emph{equivalences} on
labels.  Therefore, the constructive type theory that we work in is
\emph{homotopy type theory} (HoTT) \cite{hottbook}, a theory that can naturally
express these computationally relevant equivalences.

More specifically, the contributions of this paper are:

\begin{itemize}
\item We define the concept of \emph{species} in
  constructive type theory (\pref{sec:constructive-species}).% , characterizing
  % them as functors from a finite collection of labels to structures.
\item As part of our port to type theory, we generalize common operations on
  species, including sum, partitional and Cartesian product,
  carefully analyzing their requirements to insure consistency
  with our new interpretation.
% remove 'arithmetic product' from this list since it is far from 'common'!
\item This generalization leads to new insights. In particular, we observe
  that arithmetic product arises from Day convolution (\pref{sec:day}).
\end{itemize}

In the next section, we review the set-theoretic definitions of species (\pref{sec:species}),
before recasting them in the context of homotopy type theory in
\pref{sec:prelim}.  We assume familiarity with dependent type theory and
(basic) category throughout, but will spell out the basic HoTT tools
we need, as well as more advanced categorical constructions.

\section{Species in set theory}
\label{sec:species}

In set theory, we define species as \emph{labeled structures}---structures
that are \emph{indexed by} a set of labels.  A labeled structure is a mapping
from a given set of labels to all the shapes built from them, with some extra
properties to guarantee that we really do get the same family of shapes no
matter what set of labels we happen to choose.

For example, the species $\L$ of \emph{lists} (or \emph{linear orderings})
sends every set of labels (of size $n$) to the set of all sequences (of size
$n!$) containing each label exactly once. %(\pref{fig:lists}).
Similarly, the
species of \emph{(rooted, ordered) binary trees} sends every set of labels to
the set of all binary trees built over those labels.
% (\pref{fig:binary-trees}).
Other species describe non-algebraic data structures, such as cycles, bags and
permutations.

%\chaptertodo{More examples.  Cycles, bags.  Permutations.  Examples of
%    algebra: describe lists and trees algebraically, etc.}
%
%   \begin{figure}
%     \centering
%     \begin{diagram}[width=400]
% import SpeciesDiagrams
% import Data.List
% import Data.List.Split

% dia =
%   hcat' (with & sep .~ 0.5)
%   [ unord (map labT [0..2])
%   , mkArrow 2 (txt "L")
%   , enRect listStructures
%   ]
%   # centerXY
%   # pad 1.1

% drawList = hcat . intersperse (mkArrow 0.4 mempty) . map labT

% listStructures =
%     hcat' (with & sep .~ 0.7)
%   . map (vcat' (with & sep .~ 0.5))
%   . chunksOf 2
%   . map drawList
%   . permutations
%   $ [0..2]
%     \end{diagram}
%     \caption{The species $\L$ of lists}
%     \label{fig:lists}
%     %$
%   \end{figure}

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=400]
% import SpeciesDiagrams
% import Data.Tree
% import Diagrams.TwoD.Layout.Tree
% import Control.Arrow (first, second)

% dia =
%   hcat' (with & sep .~ 0.5)
%   [ unord (map labT [0..2])
%   , mkArrow 2 (txt "T")
%   , enRect treeStructures
%   ]
%   # centerXY
%   # pad 1.1

% drawTreeStruct = renderTree id (~~) . symmLayout . fmap labT

% trees []   = []
% trees [x]  = [ Node x [] ]
% trees xxs  = [ Node x [l,r]
%              || (x,xs) <- select xxs
%              , (ys, zs) <- subsets xs
%              , l <- trees ys
%              , r <- trees zs
%              ]

% treeStructures =
%     hcat' (with & sep .~ 0.5)
%   . map drawTreeStruct
%   . trees
%   $ [0..2]
%     \end{diagram}
%     \caption{The species $\T$ of binary trees}
%     \label{fig:binary-trees}
%     %$
%   \end{figure}

%\noindent In set theory, we define species as follows:
% JC: should probably use a proper LaTeX package to do inline lists...
\begin{defn}[Species (Joyal \cite{joyal,bll})]
\label{defn:species-set}
A \term{species} $F$ is a pair of mappings which sends any finite set $U$ (of
\term{labels}) to a set $F\ U$ (of \term{shapes}), and sends any bijection%
\footnote{We use the notation $U \bij V$ for any bijection between sets $U$ and
$V$.} $\sigma : U \bij V$ to a function $F\ \sigma : F\ U \to F\ V$
%  (illustrated in \pref{fig:relabeling}),
satisfying the functoriality conditions:
(1) $F\ id_U = id_{F U}$, and
(2) $F (\sigma \circ \tau) = F\ \sigma \circ F\ \tau$.
%\begin{itemize}
%\item $F\ id_U = id_{F U}$, and
%\item $F (\sigma \circ \tau) = F\ \sigma \circ F\ \tau$.
%\end{itemize}
\end{defn}

We call $F\ U$ the set of ``\mbox{$F$-shapes} with labels drawn from $U$'',
or simply ``\mbox{$F$-shapes} on $U$'', or even (when $U$ is clear from
context) just ``\mbox{$F$-shapes}''.\footnote{Margaret Readdy's English translation
  of Bergeron \etal \cite{bll} uses the word ``structure'' instead of
  ``shape'', but that word is likely to remind computer scientists of
  ``data structures'', which is the wrong association: data structures
  contain \emph{data}, whereas species shapes do not.  We choose the
  word ``shape'' to emphasize the fact that they are ``form without
  content''.} The bijection $\sigma$ is called a ``relabeling'' and $F\ \sigma$ is called the ``transport of $\sigma$ along
$F$'', or sometimes the ``relabeling of \mbox{$F$-shapes} by $\sigma$''.

The functoriality of relabeling means that the actual labels used
don't matter; we get ``the same shapes'' up to relabeling for any
label sets of the same size.  In other words, $F$'s action on all
label sets of size $n$ is determined by its action on any particular
such set: if $||U_1|| = ||U_2||$ and we know $F\ U_1$, we can
determine $F\ U_2$ by lifting an arbitrary bijection between $U_1$ and
$U_2$.  Therefore, we often take the finite set of natural numbers $[n] = \{0,
\dots, n-1\}$ as \emph{the} canonical label set of size $n$, and write
$F\ n$ for the set of $F$-shapes built from this set.

Using the language of category theory, we can give an equivalent, more
concise definition of species:
\begin{defn}
  \label{defn:species-cat}
  A \term{species} is a functor $F : \B \to \Set$, where $\B$%
\footnote{$\B$ for \emph{bijection}, a rare category named for its arrows.} 
  is the
  groupoid of finite sets whose morphisms are bijections, and
  $\Set$ is the category of sets and (total) functions.
\end{defn}

\begin{rem}
  Although these definitions say only that a species $F$ sends a bijection
  $\sigma : U \bij V$ to a \emph{function} $F\ \sigma : F\ U \to F\
  V$, the functoriality of $F$ guarantees that $F\ \sigma$
  will always be a bijection as well. 
%  In particular, $(F\ \sigma)^{-1}
%  = F\ (\sigma^{-1})$, since $F\ \sigma \comp F\ (\sigma^{-1}) = F\
%  (\sigma \comp \sigma^{-1}) = F\ id = id$, and similarly $F\
%  (\sigma^{-1}) \comp F\ \sigma = id$.
%  \bay{Better now, I hope?}\scw{Better, but perhaps we don't need to include
%  the full justification.}
\end{rem}

Porting the theory of species to a constructive setting
requires defining categories $\BT$ and $\Type$ so that a functor $\BT \to
\Type$ is a ``constructive counterpart'' to a functor $\B \to \Set$. We define
these categories in the next section.

%\scw{Is there a way to pronounce $\B$ and $\BT$? Why B in the first
%  place?} \bay{I don't know of a way to pronounce them.  The notation
%  $\B$ is quite standard and comes from Bergeron \etal (and perhaps
%  ultimately from Joyal?).  I suppose the B is for ``Bijections''?}

\todo{Should probably give a brief mention of the link to generating
  functions.}
\jc{Not in this section, I don't think it really adds anything here}

\section{Homotopy type theory and finiteness}
\label{sec:prelim}

We next define the categories $\BT$ and $\Type$ in the context of
\term{homotopy type theory} (HoTT).  Intuitively, the category $\BT$
should capture the idea of ``constructively finite types'',
corresponding to the finite sets of $\B$. Intuitively, we can define
finiteness as an equivalence to some type that we already know to be
finite.  We choose to work in HoTT because
its univalence axiom simplifies working with equivalences.  \bay{It
  goes much deeper than this; it is no longer the case that we are
  just using HoTT for convenience but could just as easily use some
  other type theory (as we tried to argue in our earlier paper).  I
  will try to write a clearer account of this later, but first I need
  to write the section explaining how coends work out in
  HoTT.}\todo{Why bother encoding finiteness in type theory?}\scw{I'm
  not sure we have a good answer to this question.}

This section begins by summarizing the most important ideas and notation of
HoTT; interested readers should consult the HoTT book~\cite{hottbook} for more
details.

% \scw{These comments would be better later, it is more of an observation than
%   an explanation.}
% We have chosen to work within \term{homotopy type theory}.  The
% choice was initially a pragmatic one, but seems increasingly like a
% canonical choice for encoding species in type theory: both have
% groupoids at their heart.

  % As it remains important in our
% setting, we give the precise definition we use, seeing as there are
% multiple constructive interpretations of finiteness.

\subsection{A fragment of homotopy type theory}
\label{sec:HoTT}

We work with a type theory equipped with an empty type \TyZero, a
unit type \TyOne (with inhabitant $\unit$), coproducts $A + B$ (with
constructors $\inl$ and $\inr$), dependent pairs $(x:A) \times
B(x)$ (with projections
$\outl$ and $\outr$), dependent functions $(x:A) \to B(x)$, a hierarchy of type
universes $\Type_0$, $\Type_1$, $\Type_2$\dots (we usually omit the
subscript from $\Type_0$), and propositional equality $A = B$.
The theory also allows inductive definitions.  We use $\N : \Type_0$
to denote the type of natural numbers, and $\Fin : \N \to \Type_0$ the
usual indexed type of canonical finite sets.

Note that although we use Agda's notation~\cite{Agda} for dependent pairs and 
functions, we occasionally use the traditional $\sum_{x : A} B(x)$ and
$\prod_{x:A} B(x)$ for emphasis, and the standard
abbreviations $A \times B$ and $A \to B$ for non-dependent pair and
function types. 
% Also,
% to reduce clutter, we sometimes make use of implicit quantification:
% free type variables in a type---like $A$ and $B$ in $A \times (B \to
% \N)$---are implicitly universally quantified, like $(A : \Type) \to (B
% : \Type) \to A \times (B \to \N)$.

The type of \term{equivalences} between $A$ and $B$, written $A \iso B$, is
definable in type theory; intuitively, an equivalence is a pair of inverse
functions $f : A \to B$ and $g : B \to A$.\footnote{The precise details are
  more subtle \cite[chap.  4]{hottbook}, but unimportant for our purposes.}
We overload the notations $\id$ and $\comp$ to denote the identity equivalence
and equivalence composition respectively; we also allow equivalences of type
$A \iso B$ to be implicitly used as functions $A \to B$ where it does not
cause confusion.
\scw{The $\mkIso$ notation doesn't seem to be used in the rest of the paper.}
% We use the notation
% $\mkIso$ for constructing equivalences from a pair of functions. That
% is, if $f : A \to B$ and $g : B \to A$ are inverse, then $f \mkIso g :
% A \iso B$; the proof that $f$ and $g$ are inverse is left implicit.

The structure of HoTT guarantees that functions are always functorial with
respect to equality. That is, if $e : x = y$ is a witness of equality between
$x$ and $y$ (informally, a ``path'' between $x$ and $y$), and $f$ is a
function of an appropriate type, then $f(x) = f(y)$.  Given $e$ we also have
$P(x) \to P(y)$ for any type family $P$, called the \term{transport} of $P(x)$
along $e$ and denoted $\transport{P}{e}$, or simply $e_*$ when $P$ is clear
from context.

HoTT includes the \emph{univalence axiom} which states that an
equivalence $A \iso B$ can be converted to the propositional equality
$A = B$ (and vice versa).  This axiom formally encodes
the mathematical practice of treating isomorphic things as
identical.  In other words, $A = B$ does not mean that $A$ and $B$ are
identical, but that they can be used interchangeably---and moreover,
interchanging them may require some work, computationally speaking.
Thus an equality $e : A = B$ can have nontrivial computational
content.  

As of yet, univalence has no direct computational interpretation, so
using it to give a computational interpretation of species may seem suspect. Note,
however, that \mbox{$\transport{X \mapsto X}{\ua(f)} = f$}, where $\ua : (A
\iso B) \to (A = B)$ denotes (one direction of) the univalence
axiom. So univalence introduces no computational problems as long as
applications of $\ua$ are only ultimately used via
$\mathsf{transport}$. \scw{We should ensure that our applications have
  this property.}  Univalence allows a
convenient shorthand: packaging up an equivalence into a path
and then transporting along that path results in ``automatically''
inserting the equivalence and its inverse in all the necessary places
throughout the term.

%\todo{Explain propositional truncation}

\subsection{Finiteness}
\label{sec:finiteness}

Recall that $\B$ denotes the groupoid
whose objects are finite sets and whose morphisms are bijections. We
construct its constructive counterpart $\BT$ in two stages. First, we 
introduce $\P$, a way to think about sets of labels in terms of natural numbers
(because the actual contents of these sets do not matter) and develop its
constructive analogue $\PT$. This simpler context brings
many of the issues surrounding constructive finiteness into focus.
We then show how to extend $\PT$ to $\BT$.

Denote by $\P$ the category whose objects are
natural numbers and whose morphisms %$\mor m n$ 
are bijections $\fin m
\bij \fin n$ (hence there are no morphisms %$\mor m n$ 
unless $m \equiv n$).  Often it is noted as trivial that $\P$
is equivalent to (in fact, a skeleton of) $\B$ and hence that
working with $\P$ rather than $\B$ when convenient is justified.

However, this equivalence is not so trivial: in particular, showing 
that $\P$ and $\B$ are \scw{what does strongly mean?}
\jc{means that $\P$ and $\B$ are strict categories, which in turn
means that they have sets of objects with decidable equality, that
the functors which demonstrate the equivalence are strict [aka
preserve equality], and that the natural transformations FG and GF
are \emph{equal} to the identity} \bay{No, that is the definition of
\emph{isomorphism} of categories, which we certainly don't
want. Strong equivalence is just the usual notion of equivalence, as
opposed to weak equivalence which only requires some other category
$X$ with essentially surjective and fully faithful functors $X \to \P$
and $X \to \B$.  See
\url{http://ncatlab.org/nlab/show/equivalence+of+categories}.  Weak
equivalence is relevant here since the difference between strong and
weak equivalence is precisely the axiom of choice---that is, the two
notions are the same in the presence of AC.  Anyway, I think a careful
discussion of this should go in my thesis, and we should just remove
the references to ``strong'' equivalence from the paper.}
equivalent requires the axiom of choice.  In more detail, it is easy
to define a functor $\fin - : \P \to \B$ which sends $n$ to $\fin n$
and preserves morphisms.  Defining an inverse functor $\size - : \B \to \P$ is
more problematic. We must send each set $S$ to its size $\size
S$, %(though even this is a bit suspect, from a constructive point of
%view: where exactly does this size come from?). 
and a bijection
$S \bij T$ to a bijection $\fin{\size S} \bij \fin{\size
  T}$. Intuitively we have no way to pick one: we would need to
decide on a way to match up the elements of each set $S$ with the set
of natural numbers $\fin{\size S}$.  It does not actually matter
what choice we make, since the results will be isomorphic in any case.
This is precisely where the axiom of choice comes in: we may use it to
arbitrarily choose bijections between each set $S$ and the
corresponding set of natural numbers $\fin{\size S}$.

\newcommand{\AC}{\mathsf{AC}}

% Several variants of the axiom of choice can be expressed within
% homotopy type theory.  A ``na\"ive'' variant, referred to as
% $\AC_\infty$, is given by
% \begin{equation} \tag{$\AC_\infty$}
%   \label{eq:ac-infty}
%   \left( \prod_{x : X} \sum_{(a : A(x))} P(x,a) \right) \iso \left(
%     \sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x)) \right)
% \end{equation}
% This variant is actually \emph{provable} within the theory; however,
% it is of little use here, since rather than just requiring a family of
% ``nonempty'' sets, it actually requires, for each $x$, an explicit
% \emph{witness} $a : A(x)$ for which the property $P(x,a)$ holds.  That
% is, it requires that we have already made a choice for each $x$.

The axiom of choice ($\AC$ below) is consistent with
HoTT.\scw{I think we can omit this equation for space too. Cut it.}
% \begin{equation} \tag{$\AC$}
%   \label{eq:AC}
%   \left( \prod_{x : X} \ptrunc{\sum_{(a : A(x))} P(x,a)} \right) \to
%     \ptrunc{\sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x))}
% \end{equation}
However, this axiom has no computational interpretation, and is therefore
unsuitable for constructing a functor with computational content.
%
As is standard constructive practice, we reject this use of $\AC$.
%We therefore reject the use of the axiom of choice.  
%Our goal
%is to build groupoids $\PT$ and $\BT$ which are type-theoretic
%counterparts to $\P$ and $\B$, with computable functors between them
%witnessing their equivalence.
Defining a counterpart to $\P$ is straightforward:
\begin{defn}
  $\PT$ is the groupoid where (1) the objects are values of type $\N$,
  and (2) the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
    \scw{I'm not sure I understand what this means. How does
      it type check?}\bay{Between any two objects there has to be a
      set of morphisms.  We simply define the set of morphisms between
      $m$ and $n$ to be inhabitants of the type $\Fin m \iso \Fin n$.
      (Of course, there are no inhabitants unless $m = n$.) Does that
      make sense?  What is it that confuses you?  How could we make
      this clearer?}\scw{Ok. I was thinking of $\Fin m \iso \Fin n$ as a 
      function, but then it has the wrong ``type''. But morphisms are not functions.}
\end{defn}

\todo{There is something funny going on here with groupoids
  vs. $\infty$-groupoids.  Should figure out how much of a difference
  this makes.  At the very least we should mention that we are aware
  of the issues.}\scw{???}

Constructing a counterpart to $\B$ is more subtle. What does
it mean, constructively, for a type to be finite?  There are actually
several possible answers to this question
\cite{finite}. Taking our cue from the discussion above, we note that what was
missing was a choice of bijections $S \bij \fin{\size S}$: such bijections can
be thought of as evidence of the finiteness of $S$.  This is the most
straightforward definition of constructive finiteness, and the one we adopt
here.  More formally, 
%a finite type is one with some natural number size $n$,
%and an equivalence between the type and $\Fin n$. That is, 
finite types are inhabitants of $\FinType$, where
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \]

We need to build a groupoid having such finite types as objects, and
equivalences between them as morphisms.  Via univalence, we may
conveniently package up such equivalences as paths.  We note
the following method to build an $\infty$-groupoid out of any
type:
\begin{defn}
  For a type $A$, the $\infty$-groupoid $\tygrpd{A}$ has 
  values $a : A$ as its objects, paths $a = b$ as its $1$-morphisms,
  paths between paths as $2$-morphims, and so on.
\end{defn}

We then naturally attempt to use $\tygrpd{\FinType}$ as a constructive
counterpart to $\B$.  Unfortunately, this does not work! Intuitively, the
problem is that the paths involve not just the types in question
but also between the evidence of their finiteness, so that a path
between two types requires them to be finite ``in the same way''. The
situation can be pictured as shown in \pref{fig:fin-equiv}. The
elements of types $A_1$ and $A_2$ are shown on the sides; the evidence
of their finiteness is represented by bijections between their
elements and the elements of $\Fin n$, shown along the bottom.  The
catch is that the diagram necessarily contains only triangles:
corresponding elements of $A_1$ and $A_2$ must correspond to
the same element of $\Fin n$ on the bottom row.  Therefore, there are
only two degrees of freedom: once the evidence of finiteness is
determined, there is only one valid correspondence between $A_1$ and $A_2$.
Intuitively, there should be $n!$ valid correspondences between them.
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
  \caption{A path between inhabitants of $\FinType$ contains only
    triangles}
  \label{fig:fin-equiv}
\end{figure}

\scw{We need to say explicitly why only having one morphism between any two
  objects of $\tygrpd{\FinType}$ is bad.}\jc{We sort of said so before:
  all permutations should be valid paths}

\begin{prop}
  There is at most one morphism between any two objects of
  $\tygrpd{\FinType}$.  That is, for any $X, Y : \FinType$,
  if $p_1, p_2 : X = Y$ then $p_1 = p_2$.  (Using the terminology of
  homotopy type theory, $\FinType$ is a set, \ie a $0$-type.)
\end{prop}

% \begin{proof*}{Proof (sketch).}
%   A path $(A_1, n_1, e_1) = (A_2, n_2, e_2)$ is equivalent to $(p :
%   A_1 = A_2) \times (q : n_1 = n_2) \times (q_*(p_*(e_1)) = e_2)$.
%   Noting that $p_*(e_1)$, in particular, is given by the composition
%   of $p$ with $e_1$, and \todo{finish} \jc{do we even need this proof
%   sketch?} \bay{No.}
% \end{proof*}

As having paths between evidence of finiteness imposes too strong a
constraint, we next try using the
\emph{propositional truncation}\footnote{The propositional truncation
  of a type ``squashes'' the type down to a mere proposition, by
  adding a path between every pair of inhabitants. Intuitively, this
  can be thought of as ``forgetting'' all information contained in the
  inhabitants other than their existence, though the reality is quite
  a bit more subtle.} 
of finiteness evidence.
That is, we consider $\tygrpd{\FinTypeT}$, where \[ \FinTypeT \defeq
(A : \Type) \times (n : \N) \times \ptrunc{\Fin n \iso A}. \] A path
between two inhabitants of $\FinTypeT$ is now unconstrained by the
finiteness evidence (there is always a path between any two
inhabitants of a propositional truncation), and hence equivalent to a
path between their underlying types.  This does yield the right
groupoid structure. However, we now have a different problem: we can
only prove that $\tygrpd{\FinTypeT}$ is equivalent to $\PT$ if we
treat equivalence of categories as a mere proposition. The reason is
that the recursion principle for propositional truncation only allows
making use of the contained finiteness evidence if it is in the
service of constructing an inhabitant of a mere proposition.  This
ensures that the precise content of the truncation cannot ``leak''.
However, since our goal is to construct computationally relevant
functors witnessing the equivalence, equivalence as a mere proposition
is unsatisfactory.

Instead, we define $\BT$ as follows:

\begin{defn}
Define the $\infty$-groupoid $\BT$ where
\begin{itemize}
\item the objects are values of type $\FinType \defeq (A : \Type) \times (n : \N)
\times (\Fin n \iso A)$,
\item $1$-morphisms $\mor{(A,m,i)}{(B,n,j)}$ are paths $A = B$, and
\item higher morphisms are paths between paths, and so on.
\end{itemize}
\end{defn}

That is, we do not hide finiteness evidence in a propositional
truncation, but morphisms simply ignore the finiteness evidence.  This
may seem strange: we go to the trouble of adding extra computational
evidence to objects, but then we turn around and say that the additional
evidence is irrelevant after all!  However, the point is that although the
extra evidence may be irrelevant to
\emph{morphisms}, functors out of the category may still make use of
it (see \pref{defn:size}).  Instead of having to make an arbitrary
choice of isomorphism when mapping out of an object, we ``blow up''
the category by making a separate object for each possible choice, but
ensure that objects which differ only by this choice are isomorphic.

\jc{the definition below uses $\equiv$, which has not been defined.}
\begin{rem}
  Note that given a morphism $e : \mor {(A,m,i)} {(B,n,j)}$, it is
  provably the case that $m \equiv n$.  In particular, $i \then e \then j^{-1} :
  \Fin m \iso \Fin n$, from which we may prove $m \equiv n$ by double
  induction.
\end{rem}

\begin{defn}
We define a functor, $\fin - : \PT \to \BT$ where on objects
$\fin n \defeq (\Fin n, n, \id)$, and $\fin -$ is the identity on morphisms.
\end{defn}

\begin{defn} \label{defn:size}
In the other direction, we define $\size{} : \BT \to \PT$ that sends
objects $(A, m, i)$ to $m$, an a morphism
$e : \mor {(A, m, i)} {(B, n, j)}$ is sent to $i \then e \then j^{-1}$.
% \[
%   \xymatrix{\Fin m \ar@@{<->}[d]_-i & \Fin n \\ A \ar@@{<->}[r]_e & B
%     \ar@@{<->}[u]_-{j^{-1}} } \]
The functoriality of $\size{}$ can be seen by noting the cancelling
pair of inverse equivalences in each of the following two diagrams:
  \[ \xymatrix{\Fin m \ar@@<-.4em>@@{<->}[d]_i
         \ar@@<.4em>@@{<->}[d]^{i^{-1}}
       \\
         A \ar@@(dl,dr)_{\id}
     }
     \qquad\qquad
     \xymatrix{
       \Fin m \ar@@{<->}[d]_i &
       \Fin n \ar@@<-.4em>@@{<->}[d]_j \ar@@<.4em>@@{<->}[d]^{j^{-1}} &
       \Fin o \ar@@{<->}[d]^k
     \\
       A \ar@@{<->}[r]_e &
       B \ar@@{<->}[r]_f &
       C
     }
  \]
\end{defn}

\begin{prop}
  The pair of functors $\xymatrix{\PT \ar@@<.5ex>[r]^{\fin -} & \BT
    \ar@@<.5ex>[l]^{\size{}}}$ constitutes an equivalence
  between the groupoids $\PT$ and $\BT$.

\begin{proof}
  $\size{\fin -}$ is by definition the identity functor.  The
  interesting direction is $\fin{\size -}$.
  \begin{itemize}
  \item On objects, $\fin{\size {(A,m,i)}} \equiv \fin{m} \equiv (\Fin
    m, m, \id)$, and
  \item on morphisms, $e : \mor {(A,m,i)} {(B,n,j)}$ is sent to
    $\fin{\size e} \equiv \fin{i \then e \then j^{-1}} \equiv i \then e \then j^{-1}$.
  \end{itemize}
  We must exhibit a natural isomorphism $\alpha : \nat{Id}{\fin{\size
      -}}$.  $\alpha_{(A,m,i)}$ must be a morphism
  in $\BT$ from $(A,m,i)$ to $(\Fin m, m, \id)$, that is, an
  equivalence $A \iso \Fin m$.  Therefore we define $
  \alpha_{(A,m,i)} \defeq i^{-1}$.  Naturality of $\alpha$ is given
  by the diagram
  \[ \xymatrix{
         (A,m,i) \ar[r]^-{i^{-1}} \ar[d]_e
         &
         (\Fin m, m, \id) \ar[d]^{i \then e \then j^{-1}}
       \\
         (B,n,j) \ar[r]_-{j^{-1}} & (\Fin n, n, \id)
     }
  \]
  which commutes by inspection.  Finally, we note that any natural
  transformation between functors whose codomain is a groupoid is
  automatically an isomorphism.
\end{proof}
\end{prop}

\section{Species in constructive type theory}
\label{sec:constructive-species}

We now port the theory of species to constructive type theory.

\begin{defn}
  Recall that $\Type = \Type_0$ denotes the universe of types.  We
  also denote by $\Type$ the category whose objects are values of
  $\Type_0$, and morphisms $\mor A B$ are functions.
\end{defn}

We claim that an appropriate encoding of species within homotopy type
theory is given by $[\BT, \Type]$, the category of functors from $\BT$
to $\Type$.  We cannot directly justify this by showing that
$[\B,\Set]$ and $[\BT,\Type]$ are categorically equivalent, which is
unlikely to be true.  For one, $\Set$ is ``too big'': there are many sets that
do not correspond to any type definable in type theory.

However, most working mathematicians do not actually make use of such
``exotic'' sets.  The constructions they care about
are typically precisely those which can be encoded in type theory.  In
order to justify $[\BT, \Type]$ as a constructive counterpart to $[\B,
\Set]$, therefore, we must look at what operations and constructions
are typically carried out on $[\B, \Set]$, and show that $[\BT,\Type]$
supports them as well.

To do this, we look carefully at common operations on species,
generalize them to arbitrary functors $\Lab \to \Str$, and identify precisely
what properties of $\Lab$ and $\Str$ are necessary to define them. In this
way, we start ``from scratch'' and build up a generic notion of species that
supports the operations we want.  In the process, we get a much clearer
picture of where the operations ``come from''.
In particular, $\B$ and \Set enjoy many special properties as
categories (for example, \Set is cartesian closed, has all limits and
colimits, and so on).  It is enlightening to see precisely which of these
properties are required in which situations.

After generalizing these common operations to arbitrary functor categories, we
can justify our constructive definition of species by showing that the
functor category [$\BT$,$\Type$] satisfies each required property.
In the following, to keep these various functor categories
straight, we use the terminology ``species'' for $[\B,\Set]$, ``generalized
species'' for some abstract $[\Lab, \Str]$, and ``constructive species'' for
$[\BT, \Type]$.

\section{Lifted monoids: sum and Cartesian product}

Two of the simplest operations on species are the \emph{sum} and
\emph{Cartesian product}.  As we will see, these operations are
structurally analogous: the only difference is that species sum arises
from coproducts in $\Set$ (disjoint union), whereas the Cartesian
product of species arises from products in $\Set$.

\subsection{Species sum}

The \emph{sum} of two species is given by their disjoint
union: an $(F + G)$-shape is either an $F$-shape \emph{or} a
$G$-shape (together with a tag so we can tell which).

\begin{defn}
  Given $F, G : \B \to \Set$, $F + G$ is
  defined on objects by \[ (F + G)\ L \defeq F\ L \uplus G\ L, \] where 
  $\uplus$ denotes disjoint union (coproduct) of
  sets, and the action on morphisms \[ (F + G)\
  \sigma \defeq F\ \sigma \uplus G\ \sigma, \] where $\uplus$ is
  considered as a bifunctor in the evident way. 
  % $(f \uplus g)\ (\inl\ x)
  % = \inl\ (f\ x)$ and $(f \uplus g)\ (\inr\ y) = \inr\ (g\ y)$.
\end{defn}

Thinking of species as functors in $[\P, \Set]$, we may
say that an $(F+G)$-shape of size $n$ is either an $F$-shape of size
$n$ or a $G$-shape of size $n$.

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia
%   = hcat' (with & sep .~ 1)
%     [ struct 5 "F+G"
%     , text' 1 "="
%     , vcat
%       [ struct 5 "F"
%       , text' 0.5 "OR"
%       , struct 5 "G"
%       ]
%       # centerY
%     ]

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Species sum}
%     \label{fig:sum}
%   \end{figure}

\begin{defn}
  The \term{zero} or \term{empty} species,
  $\Zero$, is the unique species with no shapes whatsoever.  That is,
  on objects,
    $\Zero\ L \defeq \varnothing$,
  and on morphisms $\Zero$ sends every $\sigma$ to the unique function
  $\varnothing \to \varnothing$.
\end{defn}

% As a simple example, the species $\One + \X$ corresponds to the
% familiar |Maybe| type from Haskell, with $\lab{\inl} \lab{\One}$
% playing the role of |Nothing| and $\lab{\inr} \comp \lab{\cons{x}}$
% playing the role of |Just|.  Note that $\LStr {\One + \X} L A$ is
% only inhabited for certain $L$ (those of size $0$ or $1$), and moreover that
% this size restriction determines the possible structure of an
% inhabitant.
%
% Note, can't include the above if we haven't talked about 1 or X
% yet.  And I now think a better way to organize things is by talking
% about each fundamental monoidal construction along with its unit.
% As for introduction forms, it's pretty trivial.

One can check that $(+,\Zero)$ gives a symmetric monoidal structure
to $[\B, \Set]$.
%It is easy to check that $(+,\Zero)$ forms a commutative monoid
%structure on the category of species.

Stepping back a bit, we can see that this monoidal structure on
species arises straightforwardly from the corresponding monoidal
structure on sets: the sum of two functors is defined as the pointwise
sum of their outputs, and likewise \Zero, the identity for the sum of
species, is defined as the functor which constantly, \ie pointwise,
returns $\varnothing$, the identity for the sum of sets.  This general
construction will be spelled out in \pref{sec:lifting-monoids}; but
first, we turn to the formally similar operation of \emph{Cartesian
  product}.

\subsection{Cartesian/Hadamard product}
\label{sec:cartesian}

In addition to coproducts $\Set$ also has products, given by $S \times
T = \{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as
the identity. (For convenience, we may suppose there is some canonical
choice of one-element set, $\{\star\}$; this is justified since all
one-element sets are isomorphic in \Set.)
\begin{defn}
  We can use the product structure on $\Set$ to define the
  \term{Cartesian} or \term{Hadamard product} of species, defined on
  objects by \[ (F \times G)\ L = F\ L \times G\ L. \]
\end{defn}
In the same way that an $(F + G)$-shape is either an $F$-shape
\emph{or} a $G$-shape on a given set of labels, an $(F \times
G)$-shape is both an $F$-shape \emph{and} a $G$-shape, on \emph{the
  same set of labels}.% (\pref{fig:Cartesian-product-dup}).  
There are several intuitive ways to think
about this situation. One can think of two distinct shapes, with
labels duplicated between them; one can think of the labels as
\emph{pointers} or \emph{labels} for locations in a shared memory;
%% (to be explored more in \pref{sec:sharing})
or one can think of the shapes themselves as being superimposed.

% \begin{figure}
%   \centering
%   \todo{Make a diagram. Or maybe omit it for space.}
%   \caption{Cartesian species product}
%   \label{fig:Cartesian-product-dup}
% \end{figure}

\begin{defn}
  The species of \emph{sets}, $\E$, is defined as the constant functor
  yielding $\{\star\}$, that is, \[ \E\ L = \{\star\}. \]
\end{defn}

\begin{rem}
  $\E$ is called the \term{species of sets} since there is
  exactly one structure on any set of labels, which can intuitively be
  thought of as the set of labels itself, with no additional
  structure.  In fact, since all one-element sets are isomorphic, we
  may as well define \[ \E\ L = \{L\}. \]
\end{rem}

\begin{prop}
  Up to isomorphism, $\E$ is the identity for Cartesian product.
\end{prop}

\subsection{Lifting monoids}
\label{sec:lifting-monoids}

Both these constructions generalize readily.  Any monoidal
structure $(\otimes, I, \alpha, \lambda, \rho)$ on a category $\Str$
lifts pointwise to a corresponding monoidal structure $(\lotimes,
\lifted I, \lifted \alpha, \lifted \lambda, \lifted \rho)$ on the
functor category $[\Lab, \Str]$. The basic idea is exactly the same as
the standard Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.  We omit the precise details, partly in
the interest of space, and partly because the details are
straightforward.  
% For the present purposes the intuition given by the
% above Haskell code should suffice; to understand the basic intuition
% behind the proof, the reader may enjoy proving that the above |Monoid|
% instance for |e -> a| satisfies the monoid laws if the instance for
% |a| does.

% \begin{prop}
%   The monoidal lifting defined above preserves the following properties:
%   \begin{itemize}
%   \item If $\otimes$ is symmetric, so is $\lotimes$.
%   \item If $\otimes$ is a categorical product, so is $\lotimes$.
%   \item If $\otimes$ is a categorical coproduct, so is $\lotimes$.
%   \end{itemize}
% \end{prop}

\scw{Say something like, ``thus we define the generalized versions of species
  sum and the empty species'' to make it explicit?} \bay{I am not sure
  what you mean.}\scw{I mean to make the definition of the generalized
  species sum more explicit. Here its defined informally and indirectly, so it
  is easy to miss the definition altogether.}

\begin{example}
  We note that lifting coproducts in $\Set$ to $[\B,\Set]$ yields $(+,
  \Zero)$, and likewise lifting products yields $(\times,
  \E)$.
\end{example}
% Since $(\uplus,\varnothing)$ is a coproduct structure on $\Set$, it
% follows that $(+, \Zero)$ is in fact a coproduct structure on the
% category $[\B,\Set]$ of species, and likewise $(\times, \One)$ is a
% categorical product.

\begin{example}
  In $\Type$, the coproduct of two types $A$ and $B$ is given by their
  sum, $A + B$, with the void type $\TyZero$ serving as the identity.
  We may thus lift this coproduct structure to the functor category
  $[\BT, \Type]$---or indeed to any $[\Lab, \Type]$, since no
  requirements are imposed on the domain category.
\end{example}

\begin{example}
  Similarly, categorical products in $\Type$ are given by product
  types $A \times B$, with the unit type $\TyOne$ as the identity.
  This then lifts to products on $[\BT,\Type]$ (or, again, any
  $[\Lab,\Type]$) which serve as an analogue of Cartesian product of
  species.
\end{example}

% \begin{example}
%   Take $\Lab = \cat{1}$ (the trivial category with one object and one
%   morphism). In this case, functors in $[\cat{1}, \Str]$ are just
%   objects of $\Str$, and $\lotimes$ is isomorphic to $\otimes$.
% \end{example}

% \begin{example}
%   Take $\Lab = \disc{\cat{2}}$, the discrete category with two
%   objects.  Then a functor $F : \disc{\cat{2}} \to \Str$ is just a
%   pair of objects in $\Str$.  For example, if $\Str = \Set$, a functor
%   $\disc{\cat{2}} \to \Set$ is a pair of sets.  In this case, taking
%   the lifted sum $F + G$ of two functors $F,G : \disc{\cat{2}} \to
%   \Set$ corresponds to summing the pairs elementwise, that is, $(S_1,
%   T_1) + (S_2, T_2) = (S_1 \uplus S_2, T_1 \uplus T_2)$.  Another way of
%   thinking of a functor $\disc{\cat{2}} \to \Set$ is as a single
%   collection of elements where each element is tagged with one of two
%   tags (``left'' or ``right'', $0$ or $1$, \etc).  From this point of
%   view, a lifted sum can be thought of as a tag-preserving disjoint union.

%   \todo{picture?}
% \end{example}

% \begin{example}
%   As an example in a similar vein, consider $\Lab = \disc{\N}$, the
%   discrete category with natural numbers as objects.  Functors
%   $\disc{\N} \to \Str$ are countably infinite sequences of objects
%   $[S_0, S_1, S_2, \dots]$.  One way to think of this is as a
%   collection of $\Str$-objects, one for each natural number
%   \emph{size}.  For example, if $\Str = \Set$ then the sequence of
%   sets $[S_0, S_1, S_2, \dots]$ can be thought of as a single
%   collection of elements with each element tagged by its size. (This
%   ``size'' intuition is actually fairly arbitrary at this point---the
%   objects of $\disc{\N}$ are in some sense just an arbitrary countably
%   infinite set of labels, and there is no particular reason they
%   should represent ``sizes''.  However, as we will see, this intuition
%   carries through well to subsequent examples.)

%   Lifting a monoidal operation to countable sequences of objects
%   performs a ``zip'', applying the monoidal operation between matching
%   positions in the two lists: \[ [S_1, S_2, S_3, \dots] \oplus [T_1,
%   T_2, T_3, \dots] = [S_1 \oplus T_1, S_2 \oplus T_2, S_3 \oplus T_3,
%   \dots] \] If $\oplus$ can be thought of as a size-preserving
%   operation---for example, disjoint union combines two collections of
%   size-$n$ things into one collection of size-$n$ things---then
%   lifting $\oplus$ combines entire size-indexed collections in a
%   size-preserving way.
%   \todo{picture}
% \end{example}

% \begin{example}
%   Up until now we have mostly considered examples with $\Str = \Set$,
%   but any monoidal category will do.  $\Type$ works similarly to
%   $\Set$, for example, with disjoint union of sets replaced by
%   coproduct of types.  \todo{Give an example with some non-set-like
%     monoidal category.}
% \end{example}

% \begin{example}
%   All the previous examples have used a discrete category in place of
%   $\Lab$; it is instructive to see an example with nontrivial
%   morphisms involved. As the simplest nontrivial example, consider
%   $\Lab = \cat{2}$, the category with two objects $0$ and $1$ and a
%   single non-identity morphism $\mor 0 1$.  A functor $\cat{2} \to
%   \Str$ is not just a pair of objects (as with $\Lab = \disc{\cat 2}$)
%   but a pair of objects with a morphism between them: \[ S_0
%   \stackrel{f}{\longrightarrow} S_1. \] Combining two such functors
%   with a lifted monoidal operation combines not just the objects but
%   also the morphisms: \[ (S_0 \stackrel{f}{\longrightarrow} S_1)
%   \oplus (T_0 \stackrel{g}{\longrightarrow} T_1) = (S_0 \oplus T_0)
%   \stackrel{f \oplus g}{\longrightarrow} (S_1 \oplus T_1) \] This is
%   possible since the monoidal operation $\oplus$ is, by definition,
%   required to be a bifunctor.
% \end{example}

\section{Day convolution: partitional and arithmetic product}
\label{sec:day}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product, which is more generally useful than
Cartesian product, even though it is more complex to define.  In
particular,
% when species are extended to labelled structures
% (\pref{chap:labelled})
it is the partitional product which corresponds to product of
generating functions, and which gives rise to the usual notion of
product on algebraic data types.  For these reasons, partitional product
is often simply referred to as ``product'', without any modifier,
although as we have seen, the Cartesian product is the one that is
actually a categorical product.

There is also another less well-known product, \term{arithmetic
  product} \cite{Maia2008arithmetic}, which can be thought of as a
symmetric form of composition.  These two products arise in an
analogous way, via a categorical construction known as \emph{Day
  convolution}.

\subsection{Partitional product}
\label{sec:partitional-product}

The partitional product $F \sprod G$ of two species $F$
and $G$ consists of paired $F$- and $G$-shapes, but with a twist:
instead of being replicated, as in Cartesian product, the labels are
\emph{partitioned} between the two shapes.

% \todo{picture of a pair of trees with disjoint labels, or something
%   like that.}

%   \begin{figure}
%     \centering
%     \begin{diagram}[width=250]
% import SpeciesDiagrams

% theDia
%   = hcat' (with & sep .~ 1)
%     [ struct 5 "F•G"
%     , text' 1 "="
%     , vcat' (with & sep .~ 0.2)
%       [ struct 2 "F"
%       , struct 3 "G"
%       ]
%       # centerY
%     ]

% dia = theDia # centerXY # pad 1.1
%     \end{diagram}
%     \caption{Partitional species product}
%     \label{fig:product}
%   \end{figure}

\begin{defn}
  The \term{partitional} or \term{Cauchy product} of two species $F$
  and $G$ is the functor defined on objects by \[ (F \sprod G)\ L =
  \biguplus_{L_1,L_2 \vdash L} F\ L_1 \times G\ L_2 \] where
  $\biguplus$ denotes an indexed coproduct of sets, and $L_1,L_2
  \vdash L$ denotes that $L_1$ and $L_2$ constitute a partition of
  $L$, that is, $L_1 \union L_2 = L$ and $L_1 \intersect L_2 =
  \varnothing$. On bijections, $F \cdot G$ uses the action of $F$ on
  the restriction of the bijections to $L_1$, and similarly for $G$
  and $L_2$.
\end{defn}

The identity for partitional product should evidently be some species
$\One$ such that \[ (\One \cdot G)\ L = \left(\biguplus_{L_1,L_2 \vdash L}
  \One\ L_1 \times G\ L_2 \right) \iso G\ L. \] The only way for this
isomorphism to hold naturally in $L$ is if $\One\ \varnothing =
\{\star\}$ (yielding a summand of $G\ L$ when $\varnothing+L = L$) and
$\One\ L_1 = \varnothing$ for all other $L_1$ (cancelling all the
other summands).

\begin{defn}
  The unit species, $\One$, is defined by
  \[ \One\ L =
  \begin{cases}
    \{\star\} & L = \varnothing \\
    \varnothing & \text{otherwise}.
  \end{cases}
  \]
\end{defn}

\subsection{Arithmetic product}
\label{sec:arithmetic-product}

\newcommand{\aprod}{\boxtimes}

There is another, more recently discovered monoidal structre on
species known as \emph{arithmetic product} \cite{Maia2008arithmetic}.
The arithmetic product of species $F$ and $G$, written $F \aprod G$,
can intuitively be thought of as an ``$F$-assembly of cloned
$G$-shapes'', that is, an $F$-shape containing multiple copies of a
single $G$-shape.  Unlike the usual notion of composition, where the
$F$-shape would be allowed to contain many different $G$-shapes, this
notion is symmetric: an $F$-assembly of cloned $G$-shapes is
isomorphic to a $G$-assembly of cloned $F$-shapes.  Another intuitive
way to think of the arithmetic product, which points out the symmetry
more clearly, is to think of a rectangular matrix of labels, together
with an $F$-shape labelled by the rows of the grid, and a $G$-shape
labelled by the columns.  We omit a more formal definition in the
interest of space; in any case, a formal definition can be extracted
from the more general definition in terms of Day convolution in
\pref{sec:day-convolution}.  Before defining Day convolution, however,
we first give some brief intuition for the concept of a \emph{coend}.

\subsection{Coends}
\label{sec:coends}

\newcommand{\D}{\bbb{D}}

Given a bifunctor $T : \C^\op \times \C \to \D$, a \term{coend} over
$T$, denoted $\int^C T(C,C)$, is an object of $\D$.  In the specific
case when the objects of $\D$ can be thought of as sets or types with
``elements''\footnote{This definition can be made precise in full
  generality (without requiring the objects of $\D$ to have
  ``elements'') using a \emph{coequalizer}.}, the coend $\int^C
T(C,C)$ is given by a quotient of an indexed coproduct $\left( \sum_{C
    \in \C} T(C,C) \right) / \sim$.  Elements of the indexed coproduct
look like pairs $(C, t)$ where $C \in \C$ and $t \in T(C,C)$. The idea
behind the quotient is that we want to consider two pairs $(C,t)$ and
$(C', t')$ equivalent if they are related by the functoriality of $T$.
In particular, for each arrow $f : C \to C'$ in $\C$ and each $x \in
T(C',C)$, we set $(C, T(f,1)\ x) \sim (C', T(1,f)\ x)$.  That is, we
can always ``swap out $(C,t)$ for $(C',t')$'' as long as we have some
way to map from $C$ to $C'$ and the associated values $t$ and $t'$ are
related by the same mapping.

Intuitively, the functor $T$ can be thought of as an ``interface'';
$(C,t)$ is then a ``module'' with ``representation type'' $C$ and
``implementation'' $t$.  Indeed, in Haskell, the coend of $T$ is given
by the type |exists e. T e e| (or rather, by an isomorphic encoding,
since |exists| is not actually valid Haskell snytax).  $T$ is required
to be a bifunctor from $\C^\op \times \C$ since the representation
type may occur both co- and contravariantly in the interface.

\subsection{Day convolution}
\label{sec:day-convolution}

Just as sum and Cartesian product were seen to arise from the same
construction applied to different monoids, both partitional and
arithmetic product arise from \emph{Day convolution}, applied to
different monoidal structures on $\B$.

The essential idea of Day convolution, first described by Brian
Day~\cite{Day1970closed}, is to construct a monoidal structure on a
functor category $[\Lab, \Str]$ based primarily on a monoidal
structure on the \emph{domain} category $\Lab$.  In particular, Day
convolution requires
\begin{itemize}
\item a monoidal structure $\oplus$ on the domain $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie\ for any two
  objects $L_1,L_2 \in \Lab$ there is a hom-object $\Lab(L_1,L_2) \in
  \Str$ rather than a set, with approrpiate coherent notions of
  composition and identity morphisms;
\item a symmetric monoidal structure $\otimes$ on the codomain $\Str$;
\item that $\Str$ be cocomplete, and in particular
  have coends over $\Lab$.
\end{itemize}

Note that any monoidal structures will do; in particular there is no
requirement that $\oplus$ be ``sum-like'' or $\otimes$
``product-like'', though that is indeed the case for partitional
product.

\begin{defn}
  Given the above conditions, the Day convolution product of $F, G \in
  [\Lab^\op, \Str]$ is given by the coend \[ F \oast G = \int^{L_1, L_2}
  F\ L_1 \otimes G\ L_2 \otimes \Lab(-, L_1 \oplus L_2). \]
\end{defn}

\begin{rem}
  Note that $\int^{L_1, L_2} \dots$ is used as an abbrevation for a
  coend over the product category $\Lab \times \Lab$.
\end{rem}
\begin{rem}
  Since groupoids are self-dual, we may ignore the $-^\op$ in the
  common case that $\Lab$ is a groupoid.
\end{rem}

This operation is associative, and has as a unit $j(I)$ where $I$ is
the unit for $\oplus$ and $j : \Lab \to [\Lab^\op, \Str]$ is the Yoneda
embedding, that is, $j(L) = \Lab(-,L)$.

% \begin{rem}
%   Note that there are only covariant occurrences of $L_1$ and $L_2$ in
%   the above definition, which simplifies the definition of the coend.
% \end{rem}

\begin{example}
  Let's begin by looking at the traditional setting of $\Lab = \B$ and
  $\Str = \Set$.  Though $\B$ does not have coproducts, it does have a
  monoidal structure given by disjoint union.  $\B$ is indeed enriched
  over $\Set$, which is also cocomplete and has a symmetric monoidal
  structure given by Cartesian product.

  Specializing the definition to this case, and expressing the coend
  as a quotient, we obtain
  \begin{align*}
    (F \cdot G)(L) &= \int^{L_1, L_2} F\ L_1 \times G\ L_2 \times
    (L \iso L_1 + L_2) \\
    &= \left( \biguplus_{L_1, L_2} F\ L_1 \times G\ L_2 \times (L \iso L_1
      + L_2) \right) \Big/ \sim
  \end{align*}
  where every pair of bijections $\sigma_i : L_i \iso L_i'$ induces
  equivalences of the form $(L_1, L_2, f, g, i) \sim (L_1', L_2', F\
  \sigma_1\ f, G\ \sigma_2\ g, (\sigma_1 + \sigma_2) \comp i)$.  In
  other words, we ``cannot tell apart'' any two summands related by a
  pair of relabellings.  The only way to tell two summands apart is if
  their respective values of $L_1$ and $L_2$ stand in a different
  relation to $L$, as witnessed by the isomorphism.  Therefore, all
  the equivalence classes can be represented canonically by a
  partition of $L$ into two disjoint subsets, giving rise to the
  earlier definition: \[ (F \sprod G)\ L =
  \biguplus_{L_1,L_2 \vdash L} F\ L_1 \times G\ L_2. \]

  Also, in this case, the identity element is $j(I) = j(\varnothing) =
  \B(-,\varnothing)$, that is, the species which takes as input a
  label set $L$ and constructs the set of bijections between $L$ and
  the empty set.  Clearly there is exactly one such bijection when $L
  = \varnothing$, and none otherwise: as expected, this is the species
  $\One$ defined in the previous section.
\end{example}

% \begin{example}
%   Although $\B$ and $\P$ are equivalent, it is still instructive to
%   work out the general definition in the case of $\P$.  There is a
%   monoidal structure on $\P$ given by addition, with $f + g : \Fin (m
%   + n) \iso \Fin (m + n)$ defined in the evident way, with $f$ acting
%   on the first $m$ values of $\Fin (m+n)$ and $g$ on the last $n$.

%   Specializing the definition,
%   \begin{align*}
%     (F \sprod G)\ n &\defeq \int^{n_1,
%       n_2} F\ n_1 \times G\ n_2 \times (\Fin n \iso \Fin {n_1} +
%     \Fin {n_2}) \\
%     &= \biguplus_{n_1 + n_2 = n} F\ n_1 \times G\ n_2
%   \end{align*}
%   that is, an $(F \sprod G)$-shape of size $n$ consists of an
%   $F$-shape of size $n_1$ and a $G$-shape of size $n_2$, where $n_1 +
%   n_2 = n$.  Indexing by labels can be seen as a generalization (a
%   \emph{categorification}, in fact) of this size-indexing scheme,
%   where we replace natural numbers with finite sets and addition with
%   disjoint union.
% \end{example}

\begin{example}
  There is another monoidal structure on $\B$ corresponding to the
  Cartesian product of sets. If we instantiate the framework of Day
  convolution with this product-like monoidal structure instead of the
  coproduct-like structure used to define partitional product---but
  keep everything else the same, in particular continuing to use
  products on $\Set$---we obtain the arithmetic product.
\end{example}

% \begin{example}
%   Let's examine this in detail in the case of $[\P,\Set]$.  The
%   monoidal structure on $\P$ is defined on objects as $m \otimes n =
%   mn$.  On morphisms, given $f : \fin m \bij \fin m$ and $g : \fin n
%   \bij \fin n$, we have $f \otimes g : \fin{mn} \bij \fin{mn}$ defined
%   by \todo{finish}.

%   Instantiating the definition of Day convolution yields
%   \begin{align*}
%     (F \boxtimes G)\ n &= \int^{n_1,n_2} F\ n_1 \times G\ n_2 \times
%     \P(n, n_1n_2) \\
%     &= \int^{n_1,n_2} F\ n_1 \times G\ n_2 \times (\fin n \bij \fin
%     {n_1 n_2}) \\
%     &= ? \\
%     &= \biguplus_{d \mid n} F\ d \times G\ (n/d)
%   \end{align*}

%   % where $\otimes$ denotes the product monoidal structure on $\B$.
%   % We cannot write this quite as nicely as partitional product, since
%   % there is no canonical way to decompose
% \end{example}

\begin{example}
  It remains to verify that $\BT$ and $\Type$ have the right properties.
%  \begin{itemize}
%  \item 
Similarly to $\B$, there are (at least) two monoidal
    structures on $\BT$, corresponding to the coproduct and product of
    types, respectively.  Note that in each case, the finiteness
    evidence for types $A$ and $B$ can be combined in a canonical way
    to construct finiteness evidence for the types $A + B$ and $A
    \times B$, respectively.
%  \item 
$\BT$ is indeed enriched over $\Type$, since the class of
    arrows between $(A,m,i)$ and $(B,n,j)$ is given by the type $A
    \iso B$.
%  \item 
We have already seen that there is a symmetric monoidal
    structure on $\Type$ given by the product of types.
%  \item 
The last condition is the most interesting: we need to say
    what a coend over $\BT$ is in $\Type$. In fact, in this case a
    coend is just a $\Sigma$-type!  This is because the morphisms in
    $\BT$ are paths, and hence the required identifications between
    inhabitants of the $\Sigma$-type are already present---they are
    induced by transport of paths in $\BT$.
%  \end{itemize}

  Given $F,G \in [\BT,\Type]$, we can thus instantiate the definition
  of Day convolution to obtain
  \[ (F \cdot G)\ L = \sum_{L_1, L_2} F\ L_1 \times G\ L_2 \times (L
  \iso L_1 + L_2), \] and similarly for generalized arithmetic
  product.

\end{example}

\scw{We need to give an example somewhere that connects the partitional
  product and arithmetic product to actual data structures. What would we use
  these operations for?}

\section{Other constructions}


\label{sec:diff}

The \emph{derivative} $F'$ of a species $F$, well-known in the functional
programming community \cite{mcbride:derivative}, is defined by $F'\ L =
F\ (L \uplus \{\star\})$.  Intuitively, an $F'$-shape is the same as
an $F$-shape with one ``hole'' in it.  To generalize this to functor
categories $[\Lab, \Str]$, it suffices for $\Str$ to have coproducts
and a terminal object.

\label{sec:multisort}

\newcommand{\lcat}[1]{#1^*}

A \emph{multisort} species \cite[\Sect \todo{look this up}]{bll} is
one which takes as inputs multiple ``sorts'' of labels which do not
mix: the relabelling bijections of single-sort species generalize to
``multibijections'' which act separately on each different sort of
label.  It is worth noting that these can also be modelled as a
functor category, replacing the groupoid $\B$ with the groupoid
$\lcat{\B}$, whose objects are lists of finite sets and whose
morphisms are lists of bijections between corresponding list elements
\cite[Exercise \todo{look this up}]{bll}.  One can show that this
groupoid has all the required properties to enable generalized species
operations; and the same construction applies equally well to $\BT$.

% \newcommand{\emptylist}{[\,]}

% \begin{defn}
%   Given a category $\C$, define the category $\lcat{\C}$ as follows.
%   \begin{itemize}
%   \item The objects of $\lcat{\C}$ are finite (possibly empty) lists
%     $[C_1, C_2, C_3, \dots]$ of objects from $\C$.
%   \item The morphisms from $[C_1, \dots, C_n]$ to $[D_1, \dots, D_n]$
%     are lists of morphisms $[f_1, \dots, f_n]$ with $f_i : C_i \to
%     D_i$.  Note there are no morphisms $[C_1, \dots, C_m] \to [D_1,
%     \dots, D_n]$ when $m \neq n$.
%   \end{itemize}
% \end{defn}

% \todo{Need to add more text here motivating these definitions and
%   propositions.  Will go much better once I get a better sense of
%   where this all is headed exactly, and which of these properties we
%   need and why.}

% \begin{lem}
%   For any category $\C$, $\lcat{\C}$ is monoidal with list
%   concatenation |++| as the tensor product and the empty list as
%   the identity object.
% \end{lem}

% \renewcommand{\Cat}{\cat{Cat}}

% \todo{Note that $\lcat{-}$ is a functor $\Cat \to \Cat$? (Is it?)}

% \begin{defn}
%   Define the embedding functor $e : \C \to \lcat{\C}$ which sends $C$
%   to the singleton list $[C]$ and $f$ to $[f]$.
% \end{defn}

% \begin{prop}
%   $e$ is full and faithful.
% \end{prop}

% \begin{defn}
%   If $(\C, \otimes, I)$ is a monoidal category, we may define a
%   functor $F^\otimes : \lcat{\C} \to \C$ by:
%   \begin{itemize}
%   \item $F^\otimes\ \emptylist = I$
%   \item $F^\otimes\ [C_1, \dots, C_n] = C_1 \otimes \dots \otimes C_n$
%   \end{itemize}
%   and similarly for morphisms.
% \end{defn}

% \begin{prop}
%   $F^\otimes$ is a (strict) monoidal functor.
%   \begin{proof}
%     $F^\otimes\ \emptylist = I$ by definition, and it is easy to check
%     that $F^\otimes\ (\ell_1 \plus \ell_2) = F^\otimes\ \ell_1 \otimes
%     F^\otimes\ \ell_2$.
%   \end{proof}
% \end{prop}

% \begin{rem}
%   Note that $F^\otimes$ is not, in general, an isomorphism.  In
%   particular, there may exist morphisms $C_1 \otimes \dots \otimes C_n
%   \to D_1 \otimes \dots \otimes D_n$ which do not arise as a tensorial
%   product of morphisms $f_i : C_i \to D_i$.  For example, in $(\Set,
%   +)$ we may define \todo{finish me}.
% \end{rem}

% Given a functor category of generalized species $[\Lab, \Str]$, we may
% now form the category $[\lcat{\Lab}, \Str]$ of generalized multisort
% species.  In particular, $[\lcat{\B}, \Set]$ corresponds exactly to
% the notion of multisort species defined in Bergeron \etal \cite{bll}.

% \todo{Note conditions under which this preserves the structure we care
%   about.  Need $\lcat{\Lab}$ to still be enriched over $\Str$.  We
%   have shown above that $\lcat{\Lab}$ preserves relevant monoidal
%   structure.  Hmm\dots multisort corresponds particularly to
%   interpreting lists using coproduct from underlying category\dots
%   where does that come from?}

% \section{Weighted Species}
% \label{sec:weighted-species}

% \todo{General explanation and intuition for weighted species, and usual definition.}

% \newcommand{\A}{\bbb{A}}

% Given some object $A \in \Str$, consider the slice category $\Str/A$.
% We can interpret objects of $\Str/A$ as objects of $\Str$ paired with
% a ``weighting''; morphisms in $\Str/A$ are thus ``weight-preserving''
% morphisms of $\Str$.

% The first thing to note is that $\Str/A$ inherits coproducts from
% $\Str$: given two weighted objects $(X, \omega_X)$ and $(Y,
% \omega_Y)$, we can uniquely construct a weighting $(X+Y, [\omega_X,
% \omega_Y])$:
% \[ \xymatrix{ X \ar[dr]_{\omega_X} \ar[r]^-{\iota_1} & X + Y
%   \ar[d]||{[\omega_X, \omega_Y]} & Y \ar[l]^-{\iota_2}
%   \ar[dl]^{\omega_Y} \\ & A & } \] To see that this is indeed the
% coproduct $(X,\omega_X) + (Y,\omega_Y)$ in $\Str/A$, \todo{finish}

% Products in $\Str/A$ are pullbacks in $\Str$.  For example, given two
% weighted sets $(X, \omega_X)$ and $(Y, \omega_Y)$ in $\Set/A$, their
% categorical product in $\Str/A$ is the set $\{(x,y) \mid x \in X, y
% \in Y, \omega_X(x) = \omega_Y(y)\}$.  However, this is not a very
% useful notion of product in this context: intuitively, taking a
% product of weighted objects should yield a combined object with some
% sort of combined weight, instead of limiting us to cases where the
% weights match.

% Instead of requiring $\Str$ to have pullbacks, we can define a
% different sort of monoidal product on $\Str/A$ if we assume that
% $\Str$ has products and $A$ is a monoid object, that is, there exist
% morphisms $\eta : 1 \to A$ and $\mu : A \times A \to A$ satisfying
% \todo{finish}.  In this case, we may define $(X, \omega_X) \otimes (Y,
% \omega_Y)$ by
% \[\xymatrixcolsep{4pc} \xymatrix{ X \times Y \ar[r]^-{\omega_X \times \omega_Y} & A
%   \times A \ar[r]^-\mu & A. } \]  The identity for $\otimes$ is given
% by $\eta$.
% %% xymatrix{ \{\star\} \ar[r]^{!} & 1 \ar[r]^\eta & A. } \]
% One can check that $\otimes$ inherits monoidal structure from
% $A$. \todo{Finish this proof.}

% \todo{Show that this gives the usual notion of weighted species.}

% \todo{Show that this construction preserves the properties we care
%   about.}

% \todo{Give some examples.}


\label{sec:weighted}

\term{Weighted} species \cite[\Sect \todo{look this up}]{bll} can also
be modelled as functors $\B \to \Set/A$, where $\Set/A$ denotes the
slice category over some appropriate set $A$ of weights. This
generalizes appropriately to type theory as well.  Due to space
constraints, the details must be postponed to a subsequent
publication. \bay{Is there a better way to say this?  Is it worth
  saying at all?}

\scw{Maybe we should combine this entire section with the future work work
  section? Of course some of it is straightforward and the future work is
  finding a venue with enough space to explain it. But they are connected as
  more operations on species.}


\section{Related Work}
\label{sec:related}

We have been highly motivated by the wealth of work which already 
exists on species.  We survey those parts which are most immediately
applicable as an appropriate survey would in itself go over the space
limit.  \cite{bll} alone still contains a vast trove of
further examples (sometimes buried deep in the exercises!) of
relevance to programming.  From the theory side, certain fascinating
aspects like integration~\cite{Rajan93} (and more generally, the solution
of algebraic and differential equations) have not been adequately
investigated.  Furthermore, a number of variants on species
\cite{Schmitt93hopfalgebras,Menni2008,Maia2008arithmetic,aguiar2010monoidal,Mishna03b}
with nontrivial applications to combinatorics, and potential
applications to programming as well remain untapped.  We should also single
out the work of Kelly \cite{kelly:operads} on Operads, which has influenced
our presentation of Day Convolution.

Species have been the basis for many implementations in the area of
enumerative combinatorics, such as Darwin~\cite{Berg85},
\LUO~\cite{FlajoletSalvyZimmermann1989a}, combstruct~\cite{FlSa95},
Aldor-Combinat~\cite{Aldor-Combinat} and
MuPAD-Combinat~\cite{Mupad-Combinat}.  Most do not model the full
spectrum of species combinators, but make up for it by implementing
very sophisticated algorithms for enumeration and generation, both
exhaustive and random.  The Haskell species package
\cite{yorgey-2010-species,species} is a fairly direct implementation
of the theory of species.

From the categorical perspective, \emph{stuff types}
\cite{BaezDolan01,Morton2006}, brilliantly explained in Byrne's
master's thesis \cite{Byrne2005}, are directly related to
species.  Stuff types are functors from some arbitrary groupoid $X$ \emph{to}
the groupoid of finite sets and bijections.  Faithful stuff types are
equivalent to species.  Stuff types map a structure to its underlying
set of positions, rather than mapping labels to structures, giving a more
co-algebraic view of structure.  Similarly,
\emph{generalised species of structures}~\cite{Fiore08} may also be
another interesting direction.  But in all these cases, there remains
much work to be done to bridge theory and practice.

From the programming languages community, \emph{containers}
\cite{abbott_categories_2003,abbott_deriv,abbott_quotient,alti:cont-tcs,alti:lics09} are closely related to species.
Containers involve \emph{shapes} and a family of \emph{position}
types indexed by shapes.  More formally, it is a dependent pair of
types $A : \Type$ and $B : A \to \Type$ (which they write $A\lhd B$) 
yielding a functor $T_{A\lhd B} X$ defined as $\Sigma a:A. X^{B\left(a\right)}$.
Rougly, their positions and our labels correspond.
%Roughly, their positions correspond to our labels, their shapes
%correspond to our shapes, and the associated functor maps
%positions to data values, much as our mappings associate data values
%to labels.  
The basic difference is that species ``build up'' shapes
from labels, while containers ``observe'' positions contained in shapes,
an algebraic versus coalgebraic view.  Containers thus naturally 
require dependent types, while much of species theory can be dealt
with using simpler types.
%\scw{We should probably omit discussion of implementation here}
% They have developed the theory quite far; as of yet,
% however, there is no implementation of containers, nor is there a
% fully developed dictionary linking concrete structures to the
% corresponding abstract container.  
%It is thus difficult to do a deeper
%comparison of the approaches.  We can nevertheless make a few simple
%observations.  
This implies in particular that each shape is associated to a fixed,
inherent set of positions.  At present, we do not see how to reconcile
that view with sharing features, such as the Cartesian product on species.
Of course, the coalgebraic view of containers allows them to capture
useful types (such as streams) which are not species.

Shapely types \cite{jay-shapely} are closely related to containers---
see~\cite[section 8]{abbott_categories_2003} for a careful
explanation of the details.  Their results show that shapely types are
those containers which are closest to species: in many
settings of importance, shapely types are \emph{discretely finite}
containers, which essentially amounts to saying that all shapes give
rise to a finite number of positions (\ie labels).  Shapely types do
not explicitly make use of labels at all, but since they involve
\emph{lists} of data values, one may say that they implicitly make
use of labels from $\Fin n$.  
% There is thus a close relationship to
% our constructive finiteness proofs for label types.  Furthermore,
% there are claims \cite{jay-shapely} that this also corresponds to
% information about memory allocation and layout, however this is not
% detailed anywhere in the literature.

\textit{Container Types Categorically} \cite{ContainerTypesCat} defines
containers as monotone
endofunctors $F$ on \cons{Rel} (\ie \emph{relators}) which have a
\emph{membership relation}; this latter concept turns out to be a special
kind of lax natural transformation from $F$ to the identity functor.
This approach is rather difficult to adequately compare to ours.
There is overlap, but no inclusion in either direction.

\section{Future work and Conclusion}
\label{sec:future}
\label{sec:conclusion}

The most important operation we have not yet formalized is that of
\emph{composition}, where the composition $F \comp G$ of species $F$
and $G$ intuitively consists of $F$-shapes containing $G$-shapes.  It
is not yet clear whether composition imposes any additional
requirements on the categories beyond those already imposed by
partitional and arithmetic product.

One of our main motivations in carrying out this line of work has been
to ultimately extend species to \term{labelled structures} by pairing
species shapes with mappings from labels to data.  This will allow
modelling algebraic data types along with a wide class of more general
data structures. \bay{What else should we say here?  We could also
  lead off this paragraph with something like ``This work is one of
  the first steps as part of a much larger research program aiming to
  use species as\dots''?}

It should also be remarked that the objects of $\Lab$ might not correspond to
``sets'' at all.  Although our definitions are guided by the the intuition of
``sets of labels'', in the most general setting we must only think of shapes as
indexed by objects of $\Lab$, rather than shapes as ``containing labels drawn
from some set''.  We need to properly leverage this extra generality.

%\begin{ack}
%Acknowledgements
%\end{ack}

\bibliographystyle{entcs}
\bibliography{MFPS}

\end{document}
