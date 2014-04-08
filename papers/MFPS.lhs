%% -*- mode: LaTeX; compile-command: "mk" -*-

\documentclass{entcs}

\usepackage{prentcsmacro}

\providecommand{\event}{MSFP 2014}
\usepackage{breakurl}


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

%\usepackage{amsthm} %% conflicts with entcsmacro
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

% \pdfpagewidth=8.5in
% \pdfpageheight=11in

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
\newcommand{\isdefn}{\vcentcolon\equiv}

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

 Abstract.

\end{abstract}

\begin{keyword} 
Combinatorial Species, Homotopy Type Theory
\end{keyword}

\end{frontmatter}

\section{Introduction}
\label{sec:intro}

The theory of combinatorial species is a unified theory of \emph{structures},
or as a progammer might say, \emph{containers}. By a structure we mean some
sort of ``shape'' containing \emph{labelled positions} or \emph{locations},
and a mapping from those labels to data. \scw{Say more about what the theory
  is and why it is interesting....}

The theory of combinatorial species \cite{joyal,bll}, as it relates to the
theory and practice of programming languages, has long seemed to the authors
``an answer looking for a question'': the theory is too beautiful, and too
``obviously'' related to algebraic data types, to have no applications
whatsoever.
Teasing out the precise relationship between species and data types, however,
has proved challenging, for two reasons. First, combinatorialists are mainly
concerned with enumerating and generating abstract structures, not with
storing and computing with data.  Thus, in order to apply this theory in a
computational setting, there are many hidden assumptions and glossed
distinctions that must first be made explicit.  Second, being situated in
traditional mathematical practice rooted in set theory, species are usually
described in ways that are \emph{untyped} and \emph{nonconstructive}, both of
which hinder adoption and understanding in a computational context.

In more detail, our contributions are as follows:

\begin{itemize}
\item We describe a ``port'' of combinatorial species from set theory to
  constructive type theory (\pref{sec:constructive-species}), making the
  theory more directly applicable in a programming context, more accessible to
  functional programmers, and incidentally illuminating some new features of
  the theory.
\item As part of this ``port'', we generalize the most common operations on
  Species, including \scw{...}, carefully analyzing their requirements so that
  we can be sure that they are consistent with our new interpretation in Type
  Theory.
\item This generalization leads to new insights. In particular, we observe
  that arithmetic product arises from Day convolution, and give a novel
  categorical presentation of weighted species.
\end{itemize}

The constructive type theory that we work in is \emph{Homotopy Type Theory}
(HoTT) \cite{hotbook}.  Species are defined over \emph{finite} sets of labels.
In a classical setting, while finiteness is a crucial part of the definition,
it is an otherwise fairly implicit feature of the actual theory.
Combinatorialists do not need to remind themselves of this finiteness
condition, as it is a pervasive axiom that you can only ``count'' finite
collections of objects.  When ported to a constructive setting, however, the
notion of finiteness takes on nontrivial computational content and
significance.  In particular, we are naturally led to work up to
computationally relevant \emph{equivalences} on labels.  Working up to
equivalence in this way confers additional expressive power, allowing us to
model efficient label operations (\eg partition) without copying.


\section{Groupoids and Finiteness in HoTT}
\label{sec:prelim}

We have found it convenient to work within \emph{homotopy type theory}
(HoTT).  However, we do not need much complex machinery from the
theory, and simply summarize the most important ideas and notation
here; interested readers should consult the HoTT book~\cite{hottbook}
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
allows inductive definitions.  We use $\N : \Type_0$ to denote the
type of natural numbers, $\Fin : \N \to \Type_0$ the usual indexed
type of canonical finite sets, and $[-] : \Type \to \Type$ the
inductive type of polymorphic lists, with constructors $|[]| :
\prod_{A:\Type} [A]$ and $- :: - : \prod_{A:\Type} A \to [A] \to [A]$.

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
type family $P$, called the \term{transport} of $P(x)$ along $e$.
Finally, a consequence of the \emph{univalence axiom} is that an
equivalence $A \iso B$ can be converted to the propositional equality
$A = B$ (and vice versa).  The intuitive idea is to formally encode
the common mathematical practice of treating isomorphic things as
identical.  It is important to keep in mind that an equality $e : A =
B$ can thus have nontrivial computational content.  In other words, $A
= B$ means not that $A$ and $B$ are identical, but merely that they
can be used interchangeably---and moreover, interchanging them may
require some work, computationally speaking.

\subsection{Species in Constructive Type Theory}
\label{sec:constructive-species}

\section{Lifted Monoids}

\section{Day Convolution}

\section{Composition?}

\section{Multisort Species}

\section{Weighted Species}

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
work on quotient containers~\cite{abbott_quotient} is quite
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

Shapely types \cite{jay-shapely} are closely related to containers---
see~\cite[section 8]{abbott_categories_2003} for a careful
explanation of the details.  Their results show that shapely types are
those containers which are closest to labelled structures: in many
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

\section{Acknowledgements}

\bibliographystyle{entcs}
\bibliography{MFPS}

\end{document}
