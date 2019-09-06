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

\DeclareMathOperator{\DecEq}{DecEq}

\newcommand{\ssum}{\boxplus}
\newcommand{\sprod}{\boxdot}
\newcommand{\scomp}{\boxcircle}
\newcommand{\scprod}{\boxtimes}
\newcommand{\fcomp}{\boxbox}

\newcommand{\LStr}[3]{\langle #1 \rangle_{#2}(#3)}
\newcommand{\LStrE}[2]{\LStr{#1}{\bullet}{#2}}
%\newcommand{\Elim}[4]{\ensuremath{\cons{Elim}_{\LStr{#1}{#2}{#3}}\
%#4}}
\newcommand{\ElimNP}[4]{\ensuremath{\LStr{#1}{#2}{#3} \rightsquigarrow {#4}}}
\newcommand{\Elim}[4]{\ensuremath{\left(\ElimNP{#1}{#2}{#3}{#4}\right)}}
\newcommand{\elim}[1]{\ensuremath{|elim|_{#1}}}

\newcommand{\compP}{\lab{\otimes}}
\newcommand{\compA}{\lab{\oast}}
\newcommand{\compJ}{\lab{\varovee}}
\newcommand{\compB}{\lab{\varogreaterthan}}

\newcommand{\Vect}[2]{\VectOp\ #1\ #2}

\newcommand{\Path}{\lightning}

\newcommand{\StoreSym}{\Mapsto}
\newcommand{\StoreNP}[2]{\ensuremath{#1 \StoreSym #2}}
\newcommand{\Store}[2]{(\StoreNP{#1}{#2})}

\newcommand{\List}{\mathsf{List}}
\newcommand{\R}{\mathsf{R}}
\newcommand{\Part}{\mathsf{Part}}

\newcommand{\LUO}{$\Lambda$\kern -.1667em\lower .5ex\hbox{$\Upsilon$}\kern -.05em\raise .3ex\hbox{$\Omega$}}

\newcommand{\bag}[1]{\ensuremath{\Lbag #1 \Rbag}}
\newcommand{\bagop}[1]{\ensuremath{\bag{}\text{-}\Varid{#1}}}

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

\newif\ifcomments\commentsfalse

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

\def\titlerunning{Arrays as labelled structures}

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
  Brent A. Yorgey
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

\def\authorrunning{B. Yorgey, J. Carette}

\begin{document}

\maketitle

\begin{abstract}

\todo{Abstract goes here.}

\end{abstract}

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
\jc{So that $\iso$ should be $\subseteq$?}

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
  \sprod G} L {A \times B}$.  \jc{The following seems to use an
older notion of Mapping?  Shouldn't the last bit be $\Store L A$? Also,
$\times$ is actually not defined (yet!).  Lastly, where does the Finite
come from?  That also seems to be from an older version.}
Expanding the definitions of $\LStr - -
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

\jc{I am rather dubious about this whole section.  It is not wrong, but
I also don't think it is ready for prime time.  More fundamentally, I 
don't think this is the right way to go, i.e. pushing shape into the labels.}
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


\subsection{Arrays}
\label{sec:arrays}

\jc{Until we have the code in the repo back to working, I would completely
remove this.  I am not sure we can get this done in time.}
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


\bibliographystyle{plainnat}
\bibliography{SpeciesAsConstructors}

\end{document}


