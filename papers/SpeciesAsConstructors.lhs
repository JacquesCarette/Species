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
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{proof}
\usepackage{comment}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}

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

\newcommand{\lam}[2]{\lambda #1 . #2}

\newcommand{\rase}[1]{\ulcorner #1 \urcorner}
\newcommand{\lowr}[1]{\llcorner #1 \lrcorner}

\newcommand{\bij}{\leftrightarrow}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Prettyref

\usepackage{prettyref}

\newrefformat{fig}{Figure~\ref{#1}}
\newrefformat{sec}{section~\ref{#1}}
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

\begin{definition}
A \term{species} $F$ is a pair of mappings which
\begin{itemize}
\item sends any finite set $L$ (of \term{labels}) to a finite set
  $F[L]$ (of \term{shapes}), and
\item sends any bijection on finite sets $\sigma : L \bij L'$ (a
  \term{relabelling}) to a function $F[\sigma] : F[L] \to F[L']$
  (illustrated in \pref{fig:relabelling}),
\end{itemize}
satisfying the following functoriality conditions:
\begin{itemize}
\item $F[id_L] = id_{F[L]}$, and
\item $F[\sigma \circ \tau] = F[\sigma] \circ F[\tau]$.
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

We call $F[L]$ the set of ``$F$-shapes with
labels drawn from $L$'', or simply ``$F$-shapes on $L$'', or even
(when $L$ is clear from context) just ``$F$-shapes.  $F[\sigma]$
is called the ``transport of $\sigma$ along $F$'', or sometimes the
``relabelling of $F$-shapes by $\sigma$''.

Note that in the combinatorial literature, elements of $F[L]$ are
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
structure as well.

\todo{where to put formal definition of labelled structures?}

\subsection{The algebra of species}
\label{sec:algebraic}



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
}

\section{Related Work}
\label{sec:related}

\begin{itemize}
\item containers, naturally
\end{itemize}

\section{Conclusion}
\label{sec:conclusion}


%\bibliographystyle{plainnat}
%\bibliography{paper}

\end{document}
