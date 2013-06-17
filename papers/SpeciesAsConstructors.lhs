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

\specialcomment{bay}{\begingroup\color{blue}[}{ --- BAY]\endgroup}
\specialcomment{todo}{\begingroup\color{red}TODO: }{\endgroup}

% \excludecomment{bay}
% \excludecomment{todo}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Misc

\newcommand{\eg}{\emph{e.g.}\xspace}
\newcommand{\ie}{\emph{i.e.}\xspace}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\begin{document}

\title{Species Constructors}

\authorinfo{Brent A. Yorgey}
{Dept. of Computer and Information Science\\ The University of Pennsylvania\\
Philadelphia, Pennsylvania, USA}
{byorgey@@cis.upenn.edu}

\authorinfo{Jacques Carette}
{Dept. of Computing and Software\\ McMaster University\\
Hamilton, Ontario, Canada}
{carette@@mcmaster.ca}

\maketitle

\begin{abstract}

\begin{todo}
Abstract goes here.
\end{todo}

\end{abstract}

\category{D.3.2}{Programming Languages}{Applicative (functional) languages}

\terms
Languages, Types

\section{Introduction}
\label{sec:intro}

\begin{todo}
  Motivation.  ``An answer looking for a question.''  Note symmetries
  were original motivation, but drawn to labels instead.

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
\end{todo}

\section{Labelled Structures}
\label{sec:labelled}

\begin{todo}
  Pedagogical, fun examples. (Map, vector, tree, edges/triangulations)
  Enough background just-in-time.
\end{todo}

\section{Combinatorial Species}
\label{sec:species}

\begin{todo}
  Theory.
\end{todo}

\section{Labelled Structures in Haskell}
\label{sec:haskell}

\begin{todo}
  Describe our implementation.  Note that actually compiling such
  things to efficient runtime code is future work.
\end{todo}

\section{Programming with Labelled Structures}
\label{sec:programming}

\begin{todo}
  Give some examples of using our implementation.
\end{todo}

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
