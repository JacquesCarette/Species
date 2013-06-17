\documentclass[9pt,preprint,authoryear]{sigplanconf}

\usepackage{../species}

\usepackage{amsmath}
\usepackage{latexsym}
\usepackage{amssymb}
\usepackage{proof}
\usepackage{comment}
\usepackage{url}
\usepackage{xspace}
\usepackage{xcolor}

\pdfpagewidth=8.5in
\pdfpageheight=11in

\newcommand{\lam}[2]{\lambda #1 . #2}

\newcommand{\rase}[1]{\ulcorner #1 \urcorner}
\newcommand{\lowr}[1]{\llcorner #1 \lrcorner}

\newtheorem{theorem}{Theorem}
\newtheorem{proposition}{Proposition}
\newtheorem{definition}{Definition}
\newtheorem{lemma}{Lemma}

\usepackage{graphicx}
\usepackage[outputdir=diagrams/,backend=ps,extension=eps]{diagrams-latex}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% lhs2TeX

%include polycode.fmt

% Use 'arrayhs' mode, so code blocks will not be split across page breaks.
\arrayhs

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
%% Misc

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}

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

\section{Labelled Structures}
\label{sec:labelled}

Rather than diving immediately into species, we begin with an
intuitive definition of ``labelled structures'' and some examples.

The essential idea of labelled structures is to separate the notions
of container shapes and the data stored in those shapes.  Labels
provide the missing link between shapes and data, allowing one to
specify which data goes where.

Informally, a labelled shape is specified by:

\begin{itemize}
\item a finite type of labels $L$;
\item a type of data elements $A$;
\item some sort of ``shape'' containing each label from $L$ exactly
  once; and
\item a function $v : L \to A$ which maps labels to data values.
\end{itemize}

Note that shapes must contain each label exactly once, but the
function $L \to A$ need not be injective; it is perfectly possible to
have the same value of type $A$ occurring multiple times (each matched
to a different label).  The requirement that shapes contain all the
labels, with no duplicates, may seem overly restrictive; we will have
more to say about this later.  The notion of ``shape'' is also left
vague for now; a precise definition will be given in \todo{where?}.

The idea of separating shapes and data is not new \todo{citations:
  containers, shapely types, etc.}.  However, previous approaches have
left the labels \emph{implicit}.  By bringing the labels to the fore
we enable \todo{cool stuff.}

\paragraph{Algebraic data types}

Lists, trees.  Show examples.  Note this is much richer than the usual
notions of lists and trees since we can distinguish different
labellings, though for usual ADTs this is not very interesting.

\paragraph{Finite maps}

\paragraph{Vectors and arrays}

\bay{
Which are really just finite maps, with some interesting
  structure on the labels.
}

\paragraph{Cycles}

\paragraph{Structures with value-level sharing}

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

\todo{
  Theory.
}

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
