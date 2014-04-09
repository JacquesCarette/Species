%% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass{entcs}

\usepackage{prentcsmacro}

\providecommand{\event}{MSFP 2014}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

\renewcommand{\Conid}[1]{\mathsf{#1}}

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

\newcommand{\TyZero}{\ensuremath{\bot}}
\newcommand{\TyOne}{\ensuremath{\top}}
\newcommand{\unit}{\ensuremath{\star}}

\newcommand{\cons}[1]{\ensuremath{\mathsf{#1}}}

\renewcommand{\False}{\cons{F}}
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

% discrete category
\newcommand{\disc}[1]{\ensuremath{\left||#1\right||}}

% morphisms
\newcommand{\mor}[2]{\ensuremath{#1 \longrightarrow #2}}
\newcommand{\nat}[2]{\ensuremath{#1 \stackrel{\bullet}{\longrightarrow} #2}}

% flipped composition
\newcommand{\then}{\mathbin{;}}

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
\def\titlerunning{Labelled structures and combinatorial species}
\title{\titlerunning}


%% ENTCS

\author{Brent A. Yorgey}
\address{Dept. of Computer and Information Science\\
 The University of Pennsylvania\\
 Philadelphia, Pennsylvania, USA}
\author{Jacques Carette}
\address{Dept. of Computing and Software\\ McMaster University\\
 Hamilton, Ontario, Canada}
\author{Stephanie Weirich}
\address{Dept. of Computer and Information Science\\
 The University of Pennsylvania\\
 Philadelphia, Pennsylvania, USA}

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

 Abstract.\scw{Write me}

\end{abstract}

\begin{keyword}
Combinatorial Species, Homotopy Type Theory
\end{keyword}

\end{frontmatter}

\section{Introduction}
\label{sec:intro}

The theory of combinatorial species is was first set forth by
Joyal~\cite{joyal} as framework for understanding and unifying much of
\emph{enumerative combinatorics}, the branch of mathematics concerned with
counting abstract \emph{structures}. This theory provides a unified view of
such structures, presenting them in a general, compositional
framework.\scw{foreshadow various species operations here?}

From a computational point of view, there is a connection between the abstract
structures of combinatorial species and the data structures and containers
that programmers use. We can think of these structures as some sort of
``shape'' containing \emph{labeled positions} or \emph{locations}. When paired
with a mapping from those labels or positions to actual data, the theory of
species can be applied to data structures. These data structures are
familiar---they subsume algebraic datatypes, for example---so this beautiful
theory promises to enrich and expand our understanding of data.

However, teasing out the precise relationship between species and data types
has proved challenging, for two reasons. First, combinatorialists are mainly
concerned with enumerating and generating abstract structures, not with
storing and computing with data.  Thus, in order to apply this theory in a
computational setting, there are many hidden assumptions and glossed
distinctions that must first be made explicit.  Second, being situated in
traditional mathematical practice rooted in set theory, species are usually
described in ways that are \emph{untyped} and \emph{nonconstructive}, both of
which hinder adoption and understanding in a computational context.

In this paper, we create a bridge between the theory of species and the theory
and practices of programming. In particular, we ``port'' the definitions of
combinatorial species from set theory to constructive type theory, making the
theory more directly applicable in a programming context and more accessible
to functional programmers.

This port is nontrivial. In fact it took us several tries to get the
definitions that we wanted. Part of the difficulty lies in the fact that
species are defined over \emph{finite} sets of labels.  In a classical
setting, while finiteness is a crucial part of the definition, it is an
otherwise fairly implicit feature of the actual theory.  Combinatorialists do
not need to remind themselves of this finiteness condition, as it is a
pervasive axiom that you can only ``count'' finite collections of objects.
When ported to a constructive setting, however, the notion of finiteness takes
on nontrivial computational content and significance.  In particular, we are
naturally led to work up to computationally relevant \emph{equivalences} on
labels.  Therefore, the constructive type theory that we work in is
\emph{homotopy type theory} (HoTT) \cite{hotbook}, a theory that can naturally
express these computationally relavant equivalences.

More specifically, the contributions of this paper are:

\begin{itemize}
\item We define the concept of \emph{species} in
  constructive type theory (\pref{sec:constructive-species}), characterizing
  them as functors from a finite collection of labels to structures.
\item As part of our port to type theory, we generalize common
  operations on species, including sum, partitional and Cartesian
  product, arithmetic product, and composition \todo{Try to get to
    composition!}, carefully analyzing their requirements so that we
  can be sure that they are consistent with our new interpretation.
\item This generalization leads to new insights. In particular, we observe
  that arithmetic product arises from Day convolution (\pref{sec:day}), and give
  a novel categorical presentation of weighted species
  (\pref{sec:weighted-species}).
\end{itemize}

In the next section, we review the set-theoretic definitions of species,
before recasting them in the context of homotopy type theory in
\pref{sec:prelim}.

\todo{Somewhere we need to say what category theory background we
  assume (and spell out the things we don't assume).}

\section{Species in Set Theory}
\label{sec:species}

In set theory, we define species as \emph{labeled structures}---structures
that are \emph{indexed by} a set of labels.  A labeled structure is a mapping
from a given set of labels to all the shapes built from them, with some extra
properties to guarantee that we really do get the same family of shapes no
matter what set of labels we happen to choose.

For example, the species $\L$ of \emph{lists} (or \emph{linear orderings})
sends every set of labels (of size $n$) to the set of all sequences (of size
$n!$) containing each label exactly once (\pref{fig:lists}). Similarly, the
species of \emph{(rooted, ordered) binary trees} sends every set of labels to
the set of all binary trees built over those labels.
% (\pref{fig:binary-trees}).
\scw{We may not actually need these figures. Cut for space?}
Other species describe non-algebraic data structures, such as cycles, bags and
permutations.
\todo{More examples.  Cycles, bags.  Permutations.  Examples of
    algebra: describe lists and trees algebraically, etc.}

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

\noindent
In set theory, we define species as follows:
\begin{defn}[Species (Joyal \cite{joyal,bll})]
\label{defn:species-set}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $U$ (of \term{labels}) to a set $F\ U$ (of
  \term{shapes}), and
\item sends any \term{relabeling}\footnote{We use the notation $U
    \bij V$ for any bijection between finite sets $U$ and $V$.}
  $\sigma : U \bij V$ to a function $F\ \sigma : F\ U \to F\ V$
%  (illustrated in \pref{fig:relabeling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F\ id_U = id_{F\ U}$, and
\item $F (\sigma \circ \tau) = F\ \sigma \circ F\ \tau$.
\end{itemize}
\end{defn}

% \begin{figure}
%   \centering
%   \begin{diagram}[width=200]
% import           Data.Maybe                     (fromMaybe)
% import           Diagrams.TwoD.Layout.Tree

% t :: BTree Int
% t = BNode 2 (leaf 1) (BNode 3 (leaf 4) (leaf 5))

% sig :: Int -> Char
% sig = ("acebd"!!) . pred

% mkNamedNode :: IsName a => (a -> String) -> a -> Diagram B R2
% mkNamedNode sh a = (text (sh a) # scale 0.3 <> circle 0.2 # fc white) # named a

% mkNamedTree :: IsName a => (a -> String) -> BTree a -> BTree (Diagram B R2)
% mkNamedTree = fmap . mkNamedNode

% drawDiaBT :: BTree (Diagram B R2) -> Diagram B R2
% drawDiaBT
%   = maybe mempty (renderTree id (~~))
%   . symmLayoutBin

% t1 = drawDiaBT . mkNamedTree show $ t
% t2 = drawDiaBT . mkNamedTree (:[]) $ fmap sig t

% linkedTrees = hcat' (with & sep .~ 1) [t1, t2]
%   # applyAll (map conn [1..5 :: Int])
%   where
%     conn i = connectOutside'
%       (with & arrowShaft .~ selectShaft i
%             & shaftStyle %~ dashing [0.05,0.05] 0
%             & arrowHead .~ noHead
%       )
%       i (sig i)
%     selectShaft i || i `elem` [1,4] = theArc # reverseTrail
%                   || i `elem` [3,5] = theArc
%     selectShaft _ = hrule 1
%     theArc = arc (0 @@@@ deg) (75 @@@@ deg)

% dia = linkedTrees # centerXY # frame 1
%   \end{diagram}
%   \caption{Relabeling} \label{fig:relabeling}
% \end{figure}

We call $F\ U$ the set of ``$F$-shapes with labels drawn from $U$'',
or simply ``$F$-shapes on $U$'', or even (when $U$ is clear from
context) just ``$F$-shapes''.\footnote{Margaret Readdy's English translation
  of Bergeron \etal \cite{bll} uses the word ``structure'' instead of
  ``shape'', but that word is likely to remind computer scientists of
  ``data structures'', which is the wrong association: data structures
  contain \emph{data}, whereas species shapes do not.  We choose the
  word shape to emphasize the fact that they are ``form without
  content''.}  $F\ \sigma$ is called the ``transport of $\sigma$ along
$F$'', or sometimes the ``relabeling of $F$-shapes by $\sigma$''.

The functoriality of relabeling means that the actual labels used
don't matter; we get ``the same shapes'', up to relabeling, for any
label sets of the same size.  In other words, $F$'s action on all
label sets of size $n$ is determined by its action on any particular
such set: if $||U_1|| = ||U_2||$ and we know $F\ U_1$, we can
determine $F\ U_2$ by lifting an arbitrary bijection between $U_1$ and
$U_2$.  So we often take the finite set of natural numbers $[n] = \{0,
\dots, n-1\}$ as \emph{the} canonical label set of size $n$, and write
$F\ [n]$ for the set of $F$-shapes built from this set.

Using the language of category theory, we can give an equivalent, more
concise definition of species:
\begin{defn}
  A \term{species} is a functor $F : \B \to \Set$, where $\B$ is the
  groupoid of finite sets whose morphisms are bijections, and
  $\Set$ is the category of sets and (total) functions.
\end{defn}

\begin{rem}
  Although \pref{defn:species-set} only says that a species $F$ sends
  a bijection $\sigma : U \bij V$ to a \emph{function} $F\ \sigma :
  F\ U \to F\ V$, the functoriality of $F$ in fact guarantees that
  bijections must be sent to bijections. In particular, $F\ \sigma$
  always has $F(\sigma^{-1})$ as its inverse, since $F\ \sigma \comp
  F\ \sigma^{-1} = F\ (\sigma \comp \sigma^{-1}) = F\ id
  = id$. \scw{I don't understand this remark. ``the definition'' is
    \pref{defn:species-set}?} \bay{Better now, I hope?}
\end{rem}

%\subsection{Species from scratch}
%\label{sec:species-scratch}

There are several reasons to generalize the definition of species given above.
First, $\B$ and \Set enjoy many special properties as categories (for example,
\Set is cartesian closed, has all limits and colimits, and so on).  It is
enlightening to see precisely which properties are required in which
situations, and we miss this entirely if we start with the kitchen sink.  The
idea is to start ``from scratch'' and build up a generic notion of species
which support the operations we want.  Along the way, we will also get a much
clearer picture of where the operations ``come from''.\footnote{Much of this
  material has been inspired by Kelly \cite{Kelly-operads} \todo{``Operads of
    J.P. May''}, \todo{``Cartesian Closed Bicategory of Generalised Species of
    Structure''}, and \todo{``Monoidal Functors, Species, and Hopf
    Algebras''}. \scw{Perhaps this discussion would be better in related work.}}

Given two arbitrary categories $\Lab$ and $\Str$, what can we say about
functors $\Lab \to \Str$, and more generally about the functor category
$[\Lab, \Str]$?  Of course, there is no point in calling functors $\Lab \to
\Str$ ``species'' for just any old categories $\Lab$ and $\Str$.  But what
properties must $\Lab$ and $\Str$ possess to make this interesting and
worthwhile?  In particular, what properties must $\Lab$ and $\Str$ possess to
enable the sorts of operations we typically want to do on species?  \footnote{
  Note that the objects of $\Lab$ might not correspond to ``sets'' at all. 
  Although our definitions are guided by the the intuition of ``sets of
  labels'', in the most general setting we must only think of shapes as
  indexed by objects of $\Lab$, rather than shapes as ``containing labels
  drawn from some set''.  }
In the following, we discuss some specific constructions on species (when
considered as functors $\B \to \Set$), and then generalize these constructions
to arbitrary functor categories to see what properties are needed in order to
define them---\ie\ where the constructions ``come from''.

However, there is a second more important reason to generalize the
definitions. We we wish to translate the theory of species to a
constructive, computational setting, and the specific categories $\B$
and \Set are inappropriate, for reasons that we discuss below.\scw{put
  those reasons here?}  Instead, in \pref{sec:finiteness} we define
categories $\BT$ and $\Type$ so that $[\BT, \Type]$ is a
``constructive counterpart'' to $[\B, \Set]$. As long as we can show
that these type-theory based categories have the right properties, we
will be able to use them with our generalized definitions.

\section{Homotopy type theory and finiteness}
\label{sec:prelim}

We next define the categories $\BT$ and $\Type$ in the context of
\term{homotopy type theory}. This section begins by summarizing the most
important ideas and notation of HoTT; interested readers should consult the
HoTT book~\cite{hottbook} for more details.
\scw{Where do we explain why HoTT? Should we move that discussion
  here.} \bay{Well, the following paragraph was supposed to be a start
  in that direction.  Obviously it needs to be fleshed out.}

\scw{These comments would be better later, it is more of an observation than
  an explanation.}
We have chosen to work within \term{homotopy type theory} (HoTT).  The
choice was initially a pragmatic one, but seems increasingly like a
canonical choice for encoding species in type theory: both have
groupoids at their heart.

The concept of \term{finiteness} plays a central (but implicit) role
in the theory of combinatorial species, primarily through the
pervasive use of generating functions.  \todo{Why bother encoding
  finiteness in type theory?} % As it remains important in our
% setting, we give the precise definition we use, seeing as there are
% multiple constructive interpretations of finiteness.

\subsection{A fragment of homotopy type theory}
\label{sec:HoTT}

The type theory we work with is equipped with an empty type \TyZero, a
unit type \TyOne (with inhabitant $\unit$), coproducts (with
constructors $\inl$ and $\inr$), dependent pairs (with projections
$\outl$ and $\outr$), dependent functions, a hierarchy of type
universes $\Type_0$, $\Type_1$, $\Type_2$\dots (we usually omit the
subscript from $\Type_0$), and a notion of propositional equality.
The theory also allows inductive definitions.  We use $\N : \Type_0$
to denote the type of natural numbers, and $\Fin : \N \to \Type_0$ the
usual indexed type of canonical finite sets.\scw{How much do we use
  lists in this paper? The $[-]$ notation is also reused in the next
  section.} \bay{Indeed, we only use meta-mathematical lists, not
  lists in type theory. I removed the reference.}

Instead of writing the traditional $\sum_{x : A} B(x)$ for the type of
dependent pairs and $\prod_{x:A} B(x)$ for dependent functions, we
will often use the Agda-like \cite{Agda} notations $(x:A) \times
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
functorial with respect to equality. That is, if $e : x = y$ is a
witness of equality between $x$ and $y$ (informally, a ``path''
between $x$ and $y$), and $f$ is a function of an appropriate type,
then $f(x) = f(y)$.  Given $e$ we also have $P(x) \to P(y)$ for any
type family $P$, called the \term{transport} of $P(x)$ along $e$ and
notated $\transport{P}{e}$, or simply $e_*$ when $P$ is clear from
context.

Finally, a consequence of the \emph{univalence axiom} is that an
equivalence $A \iso B$ can be converted to the propositional equality
$A = B$ (and vice versa).  The intuitive idea is to formally encode
the common mathematical practice of treating isomorphic things as
identical.  It is important to keep in mind that an equality $e : A =
B$ can thus have nontrivial computational content.  In other words, $A
= B$ means not that $A$ and $B$ are identical, but merely that they
can be used interchangeably---and moreover, interchanging them may
require some work, computationally speaking.

As of yet, univalence has no direct computational interpretation, so
making use of it in a computational setting may seem suspect. Note,
however, that $\transport{X \mapsto X}{\ua(f)} = f$, where $\ua : (A
\iso B) \to (A = B)$ denotes (one direction of) the univalence
axiom. So univalence introduces no computational problems as long as
applications of $\ua$ are only ultimately used via
$\mathsf{transport}$. \scw{We should ensure that our applications have
  this property.}  In this case univalence is being used only as a
sort of convenient shorthand: packaging up an equivalence into a path
and then transporting along that path results in ``automatically''
inserting the equivalence and its inverse in all the necessary places
throughout the term being transported.

\todo{Explain propositional truncation}

\subsection{Finiteness}
\label{sec:finiteness}

Recall, from the definition of species, that $\B$ denotes the groupoid
whose objects are finite sets and whose morphisms are bijections.

Let $\fin n \defeq \{0, \dots, n-1\}$ be the set of the first $n$ natural
numbers.  Denote by $\P$ the category whose objects are natural
numbers and whose morphisms $\mor m n$ are bijections $\fin m \bij \fin
n$ (hence there are no morphisms $\mor m n$ unless $m \equiv n$).  Often it
is noted as a triviality not requiring proof that $\P$ is equivalent
to (in fact, a skeleton of) $\B$ and hence we are justified in working
with $\P$ rather than $\B$ when convenient.

However, upon digging a bit deeper it is not quite so trivial after
all: in particular, showing that $\P$ and $\B$ are (strongly)
equivalent requires the axiom of choice.  In more detail, it is easy
to define a functor $\fin - : \P \to \B$ which sends $n$ to $\fin n$
and preserves morphisms.  Defining an inverse functor $\B \to \P$ is
more problematic. Clearly we must send each set $S$ to its size $\size
S$ (though even this is a bit suspect, from a constructive point of
view: where exactly does this size come from?). However, a bijection
$S \bij T$ must be sent to a bijection $\fin{\size S} \bij \fin{\size
  T}$, and intuitively we have no way to pick one: we would need to
decide on a way to match up the elements of each set $S$ with the set
of natural numbers $\fin{\size S}$.  In one sense, it does not matter
what choice we make, since the results will be isomorphic in any case.
This is precisely where the axiom of choice comes in: we may use it to
arbitrarily choose bijections between each set $S$ and the
corresponding set of natural numbers $\fin{\size S}$.

\newcommand{\AC}{\mathsf{AC}}

Several variants of the axiom of choice can be expressed within
homotopy type theory.  A ``na\"ive'' variant, referred to as
$\AC_\infty$, is given by
\begin{equation} \tag{$\AC_\infty$}
  \label{eq:ac-infty}
  \left( \prod_{x : X} \sum_{(a : A(x))} P(x,a) \right) \iso \left(
    \sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x)) \right)
\end{equation}
This variant is actually \emph{provable} within the theory; however,
it is of little use here, since rather than just requiring a family of
``nonempty'' sets, it actually requires, for each $x$, an explicit
\emph{witness} $a : A(x)$ for which the property $P(x,a)$ holds.  That
is, it requires that we have already made a choice for each $x$.

There is another variant, referred to as $\AC_{-1}$ or simply $\AC$,
that corresponds more closely to the axiom of choice in set theory:
\begin{equation} \tag{$\AC$}
  \label{eq:AC}
  \left( \prod_{x : X} \ptrunc{\sum_{(a : A(x))} P(x,a)} \right) \to
    \ptrunc{\sum_{(g : \prod_{x:X} A(x))} \prod_{(x:X)} P(x,g(x))}
\end{equation}
While this is not provable in the theory, it is consistent to assume
it as an axiom.  However, this is unsatisfactory: as an axiom, it has
no computational interpretation, and is therefore unsuitable for
constructing a functor with computational content.

\todo{There is something funny going on here with groupoids
  vs. $\infty$-groupoids.  Should figure out how much of a difference
  this makes.  At the very least we should mention that we are aware
  of the issues.}

We therefore reject the use of the axiom of choice.  Our goal will now
be to build groupoids $\PT$ and $\BT$ which are type-theoretic
counterparts to $\P$ and $\B$, with computable functors between them
witnessing their equivalence.

First, defining a counterpart to $\P$ is straightforward:
\begin{defn}
  $\PT$ is the groupoid where
  \begin{itemize}
  \item the objects are natural numbers in our type theory, that is,
    values of type $\N$, and
  \item the morphisms $\mor m n$ are equivalences of type $\Fin m \iso
    \Fin n$.
  \end{itemize}
\end{defn}

Constructing a counterpart to $\B$, however, is more subtle. What does
it mean, constructively, for a type to be finite?  There are actually
several possible answers to this question
\cite{nlab-finiteness}. Taking our cue from the discussion above,
however, we note that what was missing was a choice of bijections $S
\bij \fin{\size S}$: such bijections can be thought of precisely as
evidence of the finiteness of $S$.  This is the most straightforward
definition of constructive finiteness, and the one we adopt here.
More formally, a finite type is one with some natural number size $n$,
and an equivalence between the type and $\Fin n$, that is, inhabitants
of $\FinType$, where
\[ \FinType \defeq (A : \Type) \times (n : \N) \times (\Fin n \iso
A). \]

We need to build a groupoid having such finite types as objects, and
equivalences between them as morphisms.  Via univalence, we may
conveniently package up such equivalences as paths.  We therefore note
the following evident way to build an $\infty$-groupoid out of any
type:
\begin{defn}
  For any type $A$, the $\infty$-groupoid $\tygrpd{A}$ has as it
  objects values $a : A$, as its $1$-morphisms paths $a = b$ between
  objects, as $2$-morphisms paths between paths, and so on.
\end{defn}

As a first try at defining a constructive counterpart to $\B$, we
therefore consider $\tygrpd{\FinType}$: finite types with paths
between them.  Unfortunately, this does not work! Intuitively, the
problem is that the paths are between not only the types in question
but also between the evidence of their finiteness, so that a path
between two types requires them to be finite ``in the same way''. The
situation can be pictured as shown in \pref{fig:fin-equiv}. The
elements of types $A_1$ and $A_2$ are shown on the sides; the evidence
of their finiteness is represented by bijections between their
elements and the elements of $\Fin n$, shown along the bottom.  The
catch is that the diagram necessarily contains only triangles:
corresponding elements of $A_1$ and $A_2$ on the sides correspond to
the same element of $\Fin n$ on the bottom row.  Therefore, there are
only two degrees of freedom: once the evidence of finiteness is
determined, there is only one valid correspondence between $A_1$ and $A_2$.
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

\begin{prop}
  There is at most one morphism between any two objects of
  $\tygrpd{\FinType}$.  That is, for any $X, Y : \FinType$,
  if $p_1, p_2 : X = Y$ then $p_1 = p_2$.  (Using the terminology of
  homotopy type theory, $\FinType$ is a set, \ie a $0$-type.)
\end{prop}

\begin{proof}
  \todo{prove me?  Or omit proof for space?  The proof involves
    unrolling the meaning of a path between sigma-types (using some
    theorems from the HoTT book), proving that the transport of an
    equivalence is given by composition (which can be proved by path
    induction), and then using path induction on $p_1$ and $p_2$ to
    show that $p_1 = p_2$ is inhabited by $\mathsf{refl}$.}
\end{proof}

Since the problem with this approach was paths between evidence of
finiteness imposing too strong of a constraint, we next try using the
\emph{propositional truncation} of finiteness evidence.  That is, we
consider $\tygrpd{\FinTypeT}$, where \[ \FinTypeT \defeq (A : \Type)
\times (n : \N) \times \ptrunc{\Fin n \iso A}. \] A path between two
inhabitants of $\FinTypeT$ is now unconstrained by the finiteness
evidence (there is always a path between any two inhabitants of a
propositional truncation), and hence equivalent to a path between
their underlying types.  This does yield the right groupoid
structure. However, we now have a different problem: we can only prove
that $\tygrpd{\FinTypeT}$ is equivalent to $\PT$ if we treat
equivalence of categories is a mere proposition. The reason is that
the recursion principle for propositional truncation only allows
making use of the contained finiteness evidence if it is in the
service of constructing an inhabitant of a mere proposition.  This
ensures that the precise content of the truncation cannot ``leak''.
However, since our goal is to construct computationally relevant
functors witnessing the equivalence, equivalence as a mere proposition
is unsatisfactory.

Our third attempt goes though, however.  Instead of relying directly
on $\tygrpd{-}$, we can define $\BT$ as follows:

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
evidence to objects, but then the next minute we turn around and say
that the additional evidence is irrelevant after all!  However, the
point is that although the extra evidence may be irrelevant to
\emph{morphisms}, functors out of the category may still make use of
it (see \pref{defn:size}).  Instead of having to make an arbitrary
choice of isomorphism when mapping out of an object, we ``blow up''
the category by making a separate object for each possible choice, but
ensure that objects which differ only by this choice are isomorphic.

\begin{rem}
  Note that given a morphism $e : \mor {(A,m,i)} {(B,n,j)}$, it is
  provably the case that $m \equiv n$.  In particular, $i \then e \then j^{-1} :
  \Fin m \iso \Fin n$, from which we may prove $m \equiv n$ by double
  induction.
\end{rem}

\begin{defn}
We can now define a functor $\fin - : \PT \to \BT$ in the evident way:
\begin{itemize}
\item On objects, $\fin n \defeq (\Fin n, n, \id)$.
\item $\fin -$ is the identity on morphisms.
\end{itemize}
\end{defn}

\begin{defn} \label{defn:size}
In the other direction, we define $\size{} : \BT \to \PT$:
\begin{itemize}
\item On objects, $\size{(A, m, i)} \defeq m$.
\item On morphisms, $e : \mor {(A, m, i)} {(B, n, j)}$ is sent to \[
  \xymatrix{\Fin m \ar@@{<->}[d]_-i & \Fin n \\ A \ar@@{<->}[r]_e & B
    \ar@@{<->}[u]_-{j^{-1}} } \]
\end{itemize}
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
    \ar@@<.5ex>[l]^{\size{}}}$ constitutes a (strong) equivalence
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
      -}}$.  The component of $\alpha$ at $(A,m,i)$ must be a morphism
  in $\BT$ from $(A,m,i)$ to $(\Fin m, m, \id)$, that is, an
  equivalence $A \iso \Fin m$.  Therefore we define \[
  \alpha_{(A,m,i)} \defeq i^{-1}. \]  Naturality of $\alpha$ is given
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

\subsection{Species in Constructive Type Theory}
\label{sec:constructive-species}

Our goal is to port the theory of species from set theory into
constructive type theory.

\begin{defn}
  Recall that $\Type = \Type_0$ denotes the universe of types.  We
  overload the notation $\Type$ to also denote the category whose
  \begin{itemize}
  \item objects are types classified by $\Type_0$, and
  \item morphisms $\mor A B$ are functions with the given type.
  \end{itemize}
\end{defn}

We claim that an appropriate encoding of species within homotopy type
theory is given by $[\BT, \Type]$, the category of functors from $\BT$
to $\Type$.  We cannot directly justify this by showing that
$[\B,\Set]$ and $[\BT,\Type]$ are categorically equivalent.  Indeed,
they are certainly \emph{not} equivalent! The problem is that $\Set$
(and similarly $\B$) are ``too big'': there are many sets which do not
correspond to any type definable in type theory.

However, most working mathematicians do not actually make use of such
``exotic'' sets.  The constructions that mathematicians care about
are typically precisely those which can be encoded in type theory.  In
order to justify $[\BT, \Type]$ as a constructive counterpart to $[\B,
\Set]$, therefore, we must look at what operations and constructions
are typically carried out on $[\B, \Set]$, and show that $[\BT,\Type]$
supports them as well.

In order to do this, we will look carefully at common operations on
species, elucidating precisely which properties of $\B$ and $\Set$ are
necessary to define them.  We then show that $\BT$ and $\Type$ share
these properties.  This approach also opens the door to other
generalizations of species which can also be shown to fit into the
same framework.  We turn first to the operations of sum and Cartesian
product of species.

\section{Lifted monoids: sum and Cartesian product}

Two of the simplest operations on species are the \emph{sum} and
\emph{Cartesian product}.  As we will see, these operations arise in
an analogous way: the only difference is that species sum comes from
the fact that $\Set$ has coproducts (disjoint union of sets), whereas
the Cartesian product of species comes from the fact that $\Set$ has
products (Cartesian product of sets).

\subsection{Species sum}

species. The intuition is that an $(F + G)$-shape is either an
$F$-shape \emph{or} a $G$-shape. Formally:

\begin{defn}
  Given species $F, G : \B \to \Set$, we may form their sum $F + G$,
  defined on objects by \[ (F + G)\ L \defeq F\ L \uplus G\ L, \] where the
  $\uplus$ on the right hand side denotes the disjoint union (coproduct) of
  sets, with the action on morphisms similarly given by \[ (F + G)\
  \sigma \defeq F\ \sigma \uplus G\ \sigma, \] where $\uplus$ is
  considered as a bifunctor in the evident way: $(f \uplus g)\ (\inl\ x)
  = \inl\ (f\ x)$ and $(f \uplus g)\ (\inr\ y) = \inr\ (g\ y)$.
\end{defn}

Thinking of species alternately as functors in $[\P, \Set]$, we may
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
  We may also define the \term{zero} or \term{empty} species,
  $\Zero$, as the unique species with no shapes whatsoever.  That is,
  on objects,
  \begin{equation*}
    \Zero\ L \defeq \varnothing,
  \end{equation*}
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

It's not hard to check that $(+,\Zero)$ forms a commutative monoid
structure on species (up to isomorphism).  Stepping back a bit, we can
see that this monoidal structure on species arises straightforwardly
from the corresponding monoidal structure on sets: the sum of two
functors is defined as the pointwise sum of their outputs, and
likewise \Zero, the identity for the sum of species, is defined as the
functor which constantly, \ie pointwise, returns $\varnothing$, the
identity for the sum of sets.

This same construction works in a much more general setting.  In fact,
any monoidal structure $(\otimes, I, \alpha, \lambda, \rho)$ on a
category $\Str$ lifts pointwise to a corresponding monoidal structure
$(\lotimes, \lifted I, \lifted \alpha, \lifted \lambda, \lifted \rho)$
on the functor category $[\Lab, \Str]$. The basic idea is exactly the
same as the standard Haskell type class instance
\begin{spec}
instance Monoid a => Monoid (e -> a) where
  mempty         = \ _ -> mempty
  f `mappend` g  = \a -> f a `mappend` g a
\end{spec}
but quite a bit more general.  We omit the precise details and proofs,
partly in the interest of space, and partly because the details are
straightforward.  For the present purposes the intuition given by the
above Haskell code should suffice; to understand the basic intuition
behind the proof, the reader may enjoy proving that the above |Monoid|
instance for |e -> a| satisfies the monoid laws if the instance for
|a| does.

\begin{prop}
  The monoidal lifting defined above preserves the following properties:
  \begin{itemize}
  \item If $\otimes$ is symmetric, so is $\lotimes$.
  \item If $\otimes$ is a categorical product, so is $\lotimes$.
  \item If $\otimes$ is a categorical coproduct, so is $\lotimes$.
  \end{itemize}
\end{prop}

Since $(\uplus,\varnothing)$ is a coproduct structure on $\Set$, it follows
that $(+, \Zero)$ is in fact a coproduct structure on the category of
species.

\begin{example}
  Take $\Lab = \cat{1}$ (the trivial category with one object and one
  morphism). In this case, functors in $[\cat{1}, \Str]$ are just
  objects of $\Str$, and a lifted monoidal operation is identical
  to the unlifted one.
\end{example}

\begin{example}
  Take $\Lab = \disc{\cat{2}}$, the discrete category with two
  objects.  Then a functor $F : \disc{\cat{2}} \to \Str$ is just a
  pair of objects in $\Str$.  For example, if $\Str = \Set$, a functor
  $\disc{\cat{2}} \to \Set$ is a pair of sets.  In this case, taking
  the lifted sum $F + G$ of two functors $F,G : \disc{\cat{2}} \to
  \Set$ corresponds to summing the pairs elementwise, that is, $(S_1,
  T_1) + (S_2, T_2) = (S_1 \uplus S_2, T_1 \uplus T_2)$.  Another way of
  thinking of a functor $\disc{\cat{2}} \to \Set$ is as a single
  collection of elements where each element is tagged with one of two
  tags (``left'' or ``right'', $0$ or $1$, \etc).  From this point of
  view, a lifted sum can be thought of as a tag-preserving disjoint union.

  \todo{picture?}
\end{example}

\begin{example}
  As an example in a similar vein, consider $\Lab = \disc{\N}$, the
  discrete category with natural numbers as objects.  Functors
  $\disc{\N} \to \Str$ are countably infinite sequences of objects
  $[S_0, S_1, S_2, \dots]$.  One way to think of this is as a
  collection of $\Str$-objects, one for each natural number
  \emph{size}.  For example, if $\Str = \Set$ then the sequence of
  sets $[S_0, S_1, S_2, \dots]$ can be thought of as a single
  collection of elements with each element tagged by its size. (This
  ``size'' intuition is actually fairly arbitrary at this point---the
  objects of $\disc{\N}$ are in some sense just an arbitrary countably
  infinite set of labels, and there is no particular reason they
  should represent ``sizes''.  However, as we will see, this intuition
  carries through well to subsequent examples.)

  Lifting a monoidal operation to countable sequences of objects
  performs a ``zip'', applying the monoidal operation between matching
  positions in the two lists: \[ [S_1, S_2, S_3, \dots] \oplus [T_1,
  T_2, T_3, \dots] = [S_1 \oplus T_1, S_2 \oplus T_2, S_3 \oplus T_3,
  \dots] \] If $\oplus$ can be thought of as a size-preserving
  operation---for example, disjoint union combines two collections of
  size-$n$ things into one collection of size-$n$ things---then
  lifting $\oplus$ combines entire size-indexed collections in a
  size-preserving way.
  \todo{picture}
\end{example}

\begin{example}
  Up until now we have mostly considered examples with $\Str = \Set$,
  but any monoidal category will do.  $\Type$ works similarly to
  $\Set$, for example, with disjoint union of sets replaced by
  coproduct of types.  \todo{Give an example with some non-set-like
    monoidal category.}
\end{example}

\begin{example}
  All the previous examples have used a discrete category in place of
  $\Lab$; it is instructive to see an example with nontrivial
  morphisms involved. As the simplest nontrivial example, consider
  $\Lab = \cat{2}$, the category with two objects $0$ and $1$ and a
  single non-identity morphism $\mor 0 1$.  A functor $\cat{2} \to
  \Str$ is not just a pair of objects (as with $\Lab = \disc{\cat 2}$)
  but a pair of objects with a morphism between them: \[ S_0
  \stackrel{f}{\longrightarrow} S_1. \] Combining two such functors
  with a lifted monoidal operation combines not just the objects but
  also the morphisms: \[ (S_0 \stackrel{f}{\longrightarrow} S_1)
  \oplus (T_0 \stackrel{g}{\longrightarrow} T_1) = (S_0 \oplus T_0)
  \stackrel{f \oplus g}{\longrightarrow} (S_1 \oplus T_1) \] This is
  possible since the monoidal operation $\oplus$ is, by definition,
  required to be a bifunctor.

  \todo{Explain how the above plays out in the case of species.}\scw{You mean
    when $\Lab$ is $\BT$? That seems to be the most important example that we
    need to cover.}
\end{example}

\subsection{Cartesian/Hadamard product}
\label{sec:cartesian}

Disjoint union is not the only monoidal structure on $\Set$. In
addition to coproducts $\Set$ also has products, given by $S \times T
= \{ (s,t) \mid s \in S, t \in T \}$, with any one-element set as the
identity. (For convenience, we may suppose there is some canonical
choice of one-element set, $\{\star\}$; this is justified since all
one-element sets are isomorphic in \Set.)
\begin{defn}
  By the discussion of the previous section, this automatically lifts
  to a pointwise product structure on species, known as the
  \term{Cartesian} or \term{Hadamard product}: \[ (F \times G)\ L = F\
  L \times G\ L. \]
\end{defn}
In the same way that an $(F + G)$-shape is either an $F$-shape
\emph{or} a $G$-shape on a given set of labels, an $(F \times
G)$-shape is both an $F$-shape \emph{and} a $G$-shape, on \emph{the
  same set of labels} (\pref{fig:Cartesian-product-dup}).  As
illustrated in the figure, there are several intuitive ways to think
about this situation. One can think of two distinct shapes, with
labels duplicated between them; one can think of the labels as
\emph{pointers} or \emph{labels} for locations in a shared memory;
%% (to be explored more in \pref{sec:sharing})
or one can think of the shapes themselves as being superimposed.

\begin{figure}
  \centering
  \todo{Make a diagram.}
  \caption{Cartesian species product}
  \label{fig:Cartesian-product-dup}
\end{figure}

\begin{defn}
  Lifting the identity element pointwise gives the species \[ \E\ L =
  \{\star\}, \] where every bijection is sent to the unique function
  $\{\star\} \to \{\star\}$.  By construction, $\E$ is the identity
  for Cartesian product of species.
\end{defn}
\begin{rem}
  $\E$ is usually called the \term{species of sets} since there is
  exactly one structure on any set of labels, which can intuitively be
  thought of as the set of labels itself, with no additional
  structure.  In fact, since all one-element sets are isomorphic, we
  may as well define \[ \E\ L = \{L\}. \]
\end{rem}

Of course, since Cartesian product is the categorical product in \Set,
Cartesian/Hadamard product is also the product in the category of
species.  Interestingly, there is a different notion of species
product (though not a categorical product) which is in some sense more
natural than Cartesian product, even though it is more complicated; it
will be explored in the next section.

\todo{Forward reference to material on closedness?}

\todo{give some examples with other categories. $\Type$.  $1/\Set$,
  \ie\ pointed sets with smash product?}

\todo{\Set is distributive, in the sense that the canonical morphism
  $X \times Y + X \times Z \to X \times (Y + Z)$ is an isomorphism.
  Is $[\B, \Set]$ distributive in the same way?  If so, does lifting
  monoids always preserve distributivity? Answers: yes, and yes.}

\scw{Shouldn't we also talk about $[\BT,\Type]$ explicitly?} \bay{Yes,
  we should.}

\section{Day convolution: partitional and arithmetic product}
\label{sec:day}

There is another notion of product for species, the \term{partitional}
or \term{Cauchy} product, which is more generally useful than
Cartesian product, even though it is more complex to define.  In
particular, when species are extended to labelled structures
(\pref{chap:labelled}) it is the partitional product, rather than
Cartesian, which gives rise to the usual notion of product on
algebraic data types.  For this reason partitional product is often
simply referred to as ``product'', without any modifier, although as
we have seen it is Cartesian product, rather than partitional product,
which is actually a categorical product.

Intuitively, the partitional product $F \sprod G$ of two species $F$
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

Formally, the partitional product of species
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

Generalizing partitional product over arbitrary functor categories is
much more complex than generalizing sum and Cartesian product, and
requires turning to a construction known as \term{Day convolution}.

\subsection{Day convolution}
\label{sec:day-convolution}

The essential idea of Day convolution, first described by Brian
Day~\cite{day-convolution}, is to construct a monoidal structure on a
functor category $[\Lab, \Str]$ based primarily on a monoidal
structure on the \emph{domain} category $\Lab$.  In particular, Day
convolution requires
\begin{itemize}
\item a monoidal structure $\oplus$ on the domain $\Lab$;
\item that $\Lab$ be \emph{enriched over} $\Str$, \ie\ for any two
  objects $L_1,L_2 \in \Lab$ there is a hom-object $\Lab(L_1,L_2) \in
  \Str$ rather than a set;
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
  [\Lab, \Str]$ is given by the coend \[ F \oast G = \int^{L_1, L_2}
  F\ L_1 \otimes G\ L_2 \otimes \Lab(-, L_1 \oplus L_2). \]
\end{defn}

This operation is associative, and has as a unit $j(I)$ where $I$ is
the unit for $\oplus$ and $j : \Lab \to [\Lab^{\text{op}}, \Str]$ is the Yoneda
embedding, that is, $j(L) = \Lab(-,L)$.

\todo{Argh! Some inconsistency going on here with $\Lab$ vs
  $\Lab^{op}$; the problem is that \eg\ $\B$ and $\P$ are self-dual so
  the problem doesn't show up with them.  Perhaps we should be using
  $[\Lab^{\mathrm{op}}, \Str]$?}

\begin{rem}
  Note that there are only covariant occurrences of $L_1$ and $L_2$ in
  the above definition, which simplifies the definition of the coend.
\end{rem}

\begin{example}
  Let's begin by looking at the traditional setting of $\Lab = \B$ and
  $\Str = \Set$.  Though $\B$ does not have coproducts, it does have a
  monoidal structure given by disjoint union.  $\B$ is indeed enriched
  over $\Set$, which is also cocomplete and has a symmetric monoidal
  structure given by Cartesian product.

  Specializing the definition to this case, we obtain
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

\begin{example}
  $\B$ and $\P$ are equivalent, of course, but it is still instructive
  to work out the general definition in the case of $\P$.  In this
  case, we have a monoidal structure on $\P$ given by addition, with
  $f + g : \Fin (m + n) \iso \Fin (m + n)$ defined in the evident way,
  with $f$ acting on the first $m$ values of $\Fin (m+n)$ and $g$ on
  the last $n$.

  Specializing the definition, \[ (F \sprod G)_n \defeq \int^{n_1,
    n_2} F_{n_1} \times G_{n_2} \times (\Fin n \iso \Fin {n_1} + \Fin {n_2})  \] that is, an
  $(F \sprod G)$-shape of size $n$ consists of an $F$-shape of size
  $n_1$ and a $G$-shape of size $n_2$, where $n_1 + n_2 = n$.
  Indexing by labels is a generalization (a \emph{categorification},
  in fact) of this size-indexing scheme, where we replace natural
  numbers with finite types, addition with coproduct, and
  multiplication with product.
\end{example}

\begin{example}
  We should verify that $\BT$ and $\Type$ have the right properties.
  \begin{itemize}
  \item \todo{Monoidal coproduct structure on $\BT$}
  \item $\BT$ is indeed enriched over $\Type$, since the class of
    arrows between $(A,m,i)$ and $(B,n,j)$ is given by the type $A
    \iso B$.
  \item There is a symmetric monoidal structure on $\Type$ given by
    the product of types.
  \item The last condition is the most interesting: we need to say
    what a coend is in $\Type$. \todo{pushouts as HITs, weak
      Sigma-types, \dots ?}
  \end{itemize}

  Given $F,G \in [\BT,\Type]$, we can thus instantiate the definition
  of Day convolution to obtain
  \begin{align*}
    (F \cdot G)(L) &= \biguplus_{L_1, L_2} F\ L_1 \times G\ L_2 \times
    (L \iso L_1 + L_2) \\
  \end{align*}
  \todo{the above needs to be a \emph{weak} Sigma-type.  Need some
    different notation.  Is there already standard notation?}
\end{example}

\todo{Show that $\BT/\PT$ along with \Type\ have the right properties,
instantiate framework to show how it comes out.}

\subsection{Arithmetic product}
\label{sec:arithmetic-product}

There is another monoidal structure on $\B$ (and similarly on $\P$ and
$\N$) corresponding to the \emph{product} of sets/natural numbers.  If
we instantiate the framework of Day convolution with this product-like
monoidal structure instead of the coproduct-like structure used to
define partitional product---but keep everything else the same, in
particular continuing to use products on $\Set$---we obtain an
operation known as \term{arithmetic product}
\cite{arithmetic-product}.

Let's examine this in detail in the case of $[\P,\Set]$.  The monoidal
structure on $\P$ is defined on objects as $m \otimes n = mn$.  On
morphisms, given $f : \fin m \bij \fin m$ and $g : \fin n \bij \fin
n$, we have $f \otimes g : \fin{mn} \bij \fin{mn}$ defined by \todo{finish}.

Instantiating the definition of Day convolution yields
\begin{align*}
  (F \boxtimes G)_n &= \int^{n_1,n_2} F_{n_1} \times G_{n_2} \times
  \P(n, n_1n_2) \\
  &= \int^{n_1,n_2} F_{n_1} \times G_{n_2} \times (\fin n \bij \fin
  {n_1 n_2}) \\
  &= ? \\
  &= \biguplus_{d \mid n} F_d \times G_{n/d}
\end{align*}

% where $\otimes$ denotes the product monoidal structure on
% $\B$.  We cannot write this quite as nicely as partitional product,
% since there is no canonical way to decompose

The intuition behind this operation is that we end up with a
``matrix'' of labels, with an $F$-shape on the ``rows'' and a
$G$-shape on the ``columns''.

\todo{picture}

\todo{examples}

\bay{How can we say that we are using ``the same'' ``product-like''
  monoidal structure in all these different categories?  Are they
  related by monoidal functors?}

\section{Composition?}

\section{Multisort Species}

\todo{General introduction to the concept of multisort species, and
  usual definition.}

\todo{The idea is to show that this fits into our general setting,
  which also widens its applicability.}

\newcommand{\lcat}[1]{#1^*}
\newcommand{\emptylist}{[\,]}

\begin{defn}
  Given a category $\C$, define the category $\lcat{\C}$ as follows.
  \begin{itemize}
  \item The objects of $\lcat{\C}$ are finite (possibly empty) lists
    $[C_1, C_2, C_3, \dots]$ of objects from $\C$.
  \item The morphisms from $[C_1, \dots, C_n]$ to $[D_1, \dots, D_n]$
    are lists of morphisms $[f_1, \dots, f_n]$ with $f_i : C_i \to
    D_i$.  Note there are no morphisms $[C_1, \dots, C_m] \to [D_1,
    \dots, D_n]$ when $m \neq n$.
  \end{itemize}
\end{defn}

\todo{Need to add more text here motivating these definitions and
  propositions.  Will go much better once I get a better sense of
  where this all is headed exactly, and which of these properties we
  need and why.}

\begin{lem}
  For any category $\C$, $\lcat{\C}$ is monoidal with list
  concatenation |++| as the tensor product and the empty list as
  the identity object.
\end{lem}

\renewcommand{\Cat}{\cat{Cat}}

\todo{Note that $\lcat{-}$ is a functor $\Cat \to \Cat$? (Is it?)}

\begin{defn}
  Define the embedding functor $e : \C \to \lcat{\C}$ which sends $C$
  to the singleton list $[C]$ and $f$ to $[f]$.
\end{defn}

\begin{prop}
  $e$ is full and faithful.
\end{prop}

\begin{defn}
  If $(\C, \otimes, I)$ is a monoidal category, we may define a
  functor $F^\otimes : \lcat{\C} \to \C$ by:
  \begin{itemize}
  \item $F^\otimes\ \emptylist = I$
  \item $F^\otimes\ [C_1, \dots, C_n] = C_1 \otimes \dots \otimes C_n$
  \end{itemize}
  and similarly for morphisms.
\end{defn}

\begin{prop}
  $F^\otimes$ is a (strict) monoidal functor.
  \begin{proof}
    $F^\otimes\ \emptylist = I$ by definition, and it is easy to check
    that $F^\otimes\ (\ell_1 \plus \ell_2) = F^\otimes\ \ell_1 \otimes
    F^\otimes\ \ell_2$.
  \end{proof}
\end{prop}

\begin{rem}
  Note that $F^\otimes$ is not, in general, an isomorphism.  In
  particular, there may exist morphisms $C_1 \otimes \dots \otimes C_n
  \to D_1 \otimes \dots \otimes D_n$ which do not arise as a tensorial
  product of morphisms $f_i : C_i \to D_i$.  For example, in $(\Set,
  +)$ we may define \todo{finish me}.
\end{rem}

Given a functor category of generalized species $[\Lab, \Str]$, we may
now form the category $[\lcat{\Lab}, \Str]$ of generalized multisort
species.  In particular, $[\lcat{\B}, \Set]$ corresponds exactly to
the notion of multisort species defined in Bergeron \etal \cite{bll}.

\todo{Note conditions under which this preserves the structure we care
  about.  Need $\lcat{\Lab}$ to still be enriched over $\Str$.  We
  have shown above that $\lcat{\Lab}$ preserves relevant monoidal
  structure.  Hmm\dots multisort corresponds particularly to
  interpreting lists using coproduct from underlying category\dots
  where does that come from?}

\section{Weighted Species}
\label{sec:weighted-species}

\todo{General explanation and intuition for weighted species, and usual definition.}

\newcommand{\A}{\bbb{A}}

Given some object $A \in \Str$, consider the slice category $\Str/A$.
We can interpret objects of $\Str/A$ as objects of $\Str$ paired with
a ``weighting''; morphisms in $\Str/A$ are thus ``weight-preserving''
morphisms of $\Str$.

The first thing to note is that $\Str/A$ inherits coproducts from
$\Str$: given two weighted objects $(X, \omega_X)$ and $(Y,
\omega_Y)$, we can uniquely construct a weighting $(X+Y, [\omega_X,
\omega_Y])$:
\[ \xymatrix{ X \ar[dr]_{\omega_X} \ar[r]^-{\iota_1} & X + Y
  \ar[d]||{[\omega_X, \omega_Y]} & Y \ar[l]^-{\iota_2}
  \ar[dl]^{\omega_Y} \\ & A & } \] To see that this is indeed the
coproduct $(X,\omega_X) + (Y,\omega_Y)$ in $\Str/A$, \todo{finish}

Products in $\Str/A$ are pullbacks in $\Str$.  For example, given two
weighted sets $(X, \omega_X)$ and $(Y, \omega_Y)$ in $\Set/A$, their
categorical product in $\Str/A$ is the set $\{(x,y) \mid x \in X, y
\in Y, \omega_X(x) = \omega_Y(y)\}$.  However, this is not a very
useful notion of product in this context: intuitively, taking a
product of weighted objects should yield a combined object with some
sort of combined weight, instead of limiting us to cases where the
weights match.

Instead of requiring $\Str$ to have pullbacks, we can define a
different sort of monoidal product on $\Str/A$ if we assume that
$\Str$ has products and $A$ is a monoid object, that is, there exist
morphisms $\eta : 1 \to A$ and $\mu : A \times A \to A$ satisfying
\todo{finish}.  In this case, we may define $(X, \omega_X) \otimes (Y,
\omega_Y)$ by
\[\xymatrixcolsep{4pc} \xymatrix{ X \times Y \ar[r]^-{\omega_X \times \omega_Y} & A
  \times A \ar[r]^-\mu & A. } \]  The identity for $\otimes$ is given
by $\eta$.
%% xymatrix{ \{\star\} \ar[r]^{!} & 1 \ar[r]^\eta & A. } \]
One can check that $\otimes$ inherits monoidal structure from
$A$. \todo{Finish this proof.}

\todo{Show that this gives the usual notion of weighted species.}

\todo{Show that this construction preserves the properties we care
  about.}

\todo{Give some examples.}

\section{Related Work}
\label{sec:related}

The work on \emph{containers}
\cite{abbott_categories_2003,abbott_deriv,abbott_quotient,alti:cont-tcs,alti:lics09}
also aims to find a more general theory of data structures which
captures a large set of ``containers''.  The resulting theory is quite
elegant.  It involves \emph{shapes} and a family of \emph{position}
types indexed by shapes.  More formally, it is a dependent pair of
types $A : \Type$ and $B : A \to \Type$ (which they write $A\lhd B$) which
yields a functor $T_{A\lhd B} X$ defined as $\Sigma a:A. X^{B\left(a\right)}$.
Roughly, their positions correspond to our labels, their shapes
correspond to our labelled shapes, and the associated functor maps
positions to data values, much as our mappings associate data values
to labels.  
\scw{Explicitly point out the technical difference in the set up: species = shapes indexed by labels,
  containers = labels indexed by shapes. Surely this must make a difference?}
\scw{We should probably omit discussion of implementation here}
% They have developed the theory quite far; as of yet,
% however, there is no implementation of containers, nor is there a
% fully developed dictionary linking concrete structures to the
% corresponding abstract container.  
%It is thus difficult to do a deeper
%comparison of the approaches.  We can nevertheless make a few simple
%observations.  
One significant difference is that in the containers
work, each shape is associated with a fixed, inherent set of
positions, whereas in our approach a shape can be used with any type
of labels.  Furthermore, for them shape is an input, while for us it
is part of what is generated.  As a result, with containers, it does
not seem that the positions can easily be given extra structure (the
work on quotient containers~\cite{abbott_quotient} is quite
involved).  There are fewer combinators for containers than for
species: for example, neither the Cartesian product nor
functorial composition\scw{composition probably won't make it here} seem to be present.  Thus there is as of yet no
theory of sharing for containers. %, nor is there a fine grained theory of
% storage.  
Having said all of that, however, containers are not restricted to
finite sets of labels, which makes them more general than species: there
are useful types (such as streams) which are containers but not species.  
\scw{Rephrase the next sentence as data vs. co-data?}
And therein seems to be the main difference: the extra
generality allows containers to encapsulate fancier types, while our
concreteness lets us uniformly and more easily model low-level concerns.

Shapely types \cite{jay-shapely} are closely related to containers---
see~\cite[section 8]{abbott_categories_2003} for a careful
explanation of the details.  Their results show that shapely types are
those containers which are closest to species: in many
settings of importance, shapely types are \emph{discretely finite}
containers, which essentially amounts to saying that all shapes give
rise to a finite number of positions (\ie labels).  Shapely types do
not explicitly make use of labels at all, but since they involve
\emph{lists} of data values, one may say that they implicitly make
use of labels from $\Fin n$.  There is thus a close relationship to
our constructive finiteness proofs for label types.  Furthermore,
there are claims \cite{jay-shapely} that this also corresponds to
information about memory allocation and layout, however this is not
detailed anywhere in the literature.

Another approach is that of \textit{Container Types Categorically}
\cite{ContainerTypesCat}.  They define containers as monotone
endofunctors $F$ on \cons{Rel} (\ie \emph{relators}) which have a
\emph{membership relation}; this latter concept turns out to be a special
kind of lax natural transformation from $F$ to the identity functor.
This approach is again rather difficult to adequately compare to ours.
There is again overlap, but no inclusion in either direction.

From the categorical perspective, \emph{stuff types}
\cite{BaezDolan01,Morton2006}, brilliantly explained in Byrne's
master's thesis \cite{Byrne2005}, are directly related to
species.  Stuff types are functors from some arbitrary groupoid $X$ to
the groupoid of finite sets and bijections.  Faithful stuff types are
equivalent to species.  But these work much like containers: stuff
types map a structure to its underlying set (which can be thought of as
positions), instead of mapping labels to structures.  In a different
direction, \emph{polynomial functors over groupoids} also generalize
species~\cite{kock2012data}, and seem a categorically solid
foundation for an even more general approach to data type
constructors.  Unfortunately, no one has yet to unravel these
definitions into something suitable for implementation.  Similarly,
\emph{generalised species of structures}~\cite{Fiore08} may also be
another interesting direction.  But in all these cases, there remains
much work to be done to bridge theory and practice.

Species have been the basis for many implementations in the area of
enumerative combinatorics, such as Darwin~\cite{Berg85},
\LUO~\cite{FlajoletSalvyZimmermann1989a}, combstruct~\cite{FlSa95},
Aldor-Combinat~\cite{Aldor-Combinat} and
MuPAD-Combinat~\cite{Mupad-Combinat}.  Most do not model the full
spectrum of species combinators, but make up for it by implementing
very sophisticated algorithms for enumeration and generation, both
exhaustive and random.  The Haskell species package
\cite{yorgey-2010-species,species} is a fairly direct implementation
of the theory of species, without attempting to use this theory as a
foundation for data structures.

Lastly, we should note that we have used but a small fraction of the
theory of species.  \cite{bll} alone still contains a vast trove of
further examples (sometimes buried deep in the exercises!) of
relevance to programming.  We have also not yet really touched the
\emph{calculus} aspects of the theory; while the derivative is by now
well-known, integration~\cite{Rajan93} has not really been explored.
There are also new variants on
species~\cite{Schmitt93hopfalgebras,Menni2008,Maia2008arithmetic,aguiar2010monoidal}
with nontrivial applications to combinatorics, and possible
applications to programming as well. Species have even been applied to
the study of attribute grammars~\cite{Mishna03b}.

\section{Future work}
\label{sec:future}

\section{Conclusion}
\label{sec:conclusion}

\begin{ack}
Acknowledgements
\end{ack}

\bibliographystyle{entcs}
\bibliography{MFPS}

\end{document}
