\documentclass[10 pt., handout]{beamer}

\usepackage{agda}

\mode<presentation>
{
  \usetheme{Warsaw}
  % or ...

  %\setbeamercovered{transparent}
  % or whatever (possibly just delete it)
}


\usepackage[english]{babel}
% or whatever

%\usepackage[latin1]{inputenc}
% or whatever

\usepackage{times}
\usepackage[T1]{fontenc}
% Or whatever. Note that the encoding and the font should match. If T1
% does not look nice, try deleting the line with the fontenc.

\newcommand{\bl}{\color{blue}}

\theoremstyle{plain}
%\newtheorem{theorem}{Theorem}[section]
%\newtheorem{lemma}[theorem]{Lemma}
%\newtheorem*{corollary}{Corollary}
%\newtheorem{proposition}[theorem]{Proposition}
\newtheorem*{quotthm}{Theorem}
\newtheorem*{question}{Question}


%\theoremstyle{definition}
%\newtheorem{definition}[theorem]{Definition}

\theoremstyle{remark}
%\newtheorem{remark}[theorem]{Remark}
%\newtheorem*{acknowledgements}{Acknowledgements}

\newcommand{\Z}{\mathbb{Z}}
\newcommand{\R}{\mathbb{R}}
\newcommand{\C}{\mathbb{C}}
\newcommand{\N}{\mathbb{N}}
\newcommand{\U}{\mathcal{U}}
\newcommand{\M}{\mathcal{M}}
\newcommand{\T}{\mathcal{T}}
\renewcommand{\L}{\mathcal{L}}
\renewcommand{\S}{\mathcal{S}}
\renewcommand{\H}{{\mathbb{H}}}
\newcommand{\F}{\mathfrak{F}}
\newcommand{\Zp}{\mathbb{Z}/p\mathbb{Z}}
\newcommand{\Zq}{\mathbb{Z}/q\mathbb{Z}}
\newcommand{\Zz}{\mathbb{Z}/2\mathbb{Z}}
\newcommand{\Zn}{\mathbb{Z}/n\mathbb{Z}}
\newcommand{\sm}{\setminus}
\newcommand{\tr}{\triangle}
\renewcommand{\i}{\bm{i}}
\renewcommand{\j}{\bm{j}}
\renewcommand{\k}{\bm{k}}
\newcommand{\co}{\colon\thinspace}
\newcommand{\del}{\partial}
\newcommand{\cc}{\mathcal{C}}
\newcommand{\tc}{\widetilde{\mathcal{C}}}

\begin{document}



\title{Foundations of Type theory for HoTT}

\author{Siddhartha Gadgil}


\institute
{
Department of Mathematics\\
  Indian Institute of Science}
  
\date{\today}

\maketitle



% If you have a file called "university-logo-filename.xxx", where xxx
% is a graphic format that can be processed by latex or pdflatex,
% resp., then you can add a logo as follows:

 \pgfdeclareimage[height=0.5cm]{university-logo}{IIScLogo}
 \logo{\pgfuseimage{university-logo}}




 


% If you wish to uncover everything in a step-wise fashion, uncomment
% the following command: 

\beamerdefaultoverlayspecification{<+->}
\begin{frame}{Foundations overview}
\begin{itemize}

\item We review the foundations of the type theory underlying homotopy type theory. 

\item This is a literate agda document.

\item We must include a module statement, matching the file name.

\begin{code}
open import Base

module Foundations where

\end{code}

\end{itemize}

\end{frame}

\begin{frame}{Axioms and Rules}

\begin{itemize}

\item Usual \emph{rigorous} mathematics is based on definitions and aioms, for example \emph{a function $f : \R \to \R$ is said to be continuous at $x$ if 
$$\forall \epsilon > 0 \exists \delta >0 \forall y \in \R (|y - x| \le \delta \implies |f(y) - f(x)| < \epsilon).$$}  

\item We however do not explicitly give rules saying why \emph{ a function $f : \R \to \R$ is said to be brown at $x$ if 
$$\forall \exists \delta \forall z \in \R (|y - f(x)| \le \delta \implies |f(y) - f(x)|)$$} makes no sense. 

\item We thus do not give rules for 
\begin{itemize}
\item What is a valid expression.
\item What it represents: term (real number, set etc) or formula (in definitions, theorems).
\item Rules for deduction.
\end{itemize}

\item We will instead give rules for what are valid expressions, and what are their types. We will need very few axioms.

\end{itemize}

\end{frame}

\begin{frame}{Contexts, terms, types, universes}

\begin{itemize}

\item A context consists of a collection of \emph{terms}.

\item Each term has a \emph{type}, mostly unique (denoted, for example, $a : A$).

\item The rules concerning a term are determined by its type.

\item Types are also terms.

\item A \emph{Universe} is a type $\U$ so that all terms with type $\U$ are themselves types.

\end{itemize}

\end{frame}

\begin{frame}{Types of rules}

We have rules that:

\begin{itemize}

\item let us form terms from other terms.

\item let us create a new context from a given context, by introducing new terms which can depend on the given context.

\item give the result of substituting one term for another (with the same type) in a given term.

\item allow us to make say that a term $a$ has a specified type $A$.

\item allow us to conclude that a pair of terms are equal (by definition).

\item give a collection of universes, which are present in all contexts.

\end{itemize}

\end{frame}



\begin{frame}{Universes}

\begin{itemize}

\item There is a sequence of universes, $\U_0$, $U_1$, $\dots$
    
\item The universe $\U_i$ has type $\U_{i+1}$. 

\item These are cumulative, with $U_i \subset U_{i+1}$.

\item If a type $T$ has type $\U_i$, it also has type $\U_{i+1}$.  


\end{itemize}

\end{frame}



\begin{frame}{Function types}

\begin{itemize}

\item If $A$ and $B$ are types, then we can form the function type $A \to B$.

\item If $f : A \to B$ is a term of a function type, and $a : A$ is a term, then $f(a)$ is a term that has type $B$.

\item We can form terms of a type $A \to B$ by using a $lambda$-expression $a \mapsto b$.

\item Here $b$ is a term of type $B$ formed from the terms in the context together with a term $a$ we introduce and declare to have type $A$, using the usual rules for forming terms.

\item If $f = a \mapsto b : A \to B$, then for $a' : A$, $f(a')$ equals, by definition, the result of substituting $a$ by $a'$ in $b$.

\end{itemize}

\end{frame}


\begin{frame}{$\Pi$-types}

\begin{itemize}

\item A \emph{type family} is a function $B : A \to \U$, where $A$ is a type and $\U$ is a universe.

\item Given a type family $B : A \to \U$, we can form the type $\Pi_{a : A} B(a)$ of dependent functions.

\item Given a dependent function $f : \Pi_{a : A} B(a)$ and a term $a : A$, we can form the term $f(a)$ with type $B(a)$.

\item We can form terms of a type $\Pi_{a : A} B(a)$ by using a $\lambda$-expression $a ↦ b$, with $b$ a term of type $B(a)$ formed from the terms in the context together with a term $a$ we introduce and declare to be of type $A$.

\item If $f = a \mapsto b : \Pi_{a: A} B(a)$, then for $a' : A$, $f(a')$ equals, by definition, the result of substituting $a$ by $a'$ in $b$.


\end{itemize}

\end{frame}



\begin{frame}{Inductive types: a first look}

\begin{itemize}

\item We can introduce into a context, simultaneously, a type $W$ \emph{inductively generated} by given \emph{constructors}, and its constructors.

\item The constructors for $W$ are terms with specified types, which may depend on $W$.

\item For example, the type $\N$ is inductively generated by the constructors
\begin{itemize}
\item $0: \N$.
\item $succ : \N \to \N$.
\end{itemize}

\item In Agda, this is

\begin{code}
data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ
\end{code}

\end{itemize}

\end{frame}

\begin{frame}{Inductive types: Lists}

\begin{itemize}

\item For each type $A$, $List(A)$ is a type inductively defined by its constructors.
\begin{itemize}
\item $[] : List(A)$.
\item $cons : A \to List(A) \to List(A)$.
\end{itemize}

\item In Agda, this is

\begin{code}
data List(A : Type) : Type where
  [] : List A
  _::_ : List A → List A → List A
\end{code}


\end{itemize}

\end{frame}




\begin{frame}{Recursion and Induction : a first look}

\begin{itemize}

  \item


\end{itemize}

\end{frame}



\begin{frame}{Families}

\begin{itemize}

  \item


\end{itemize}

\end{frame}




\begin{frame}{Constructor types for an inductive type}

\begin{itemize}

  \item


\end{itemize}

\end{frame}



\begin{frame}{Recursion for constructors having families}

\begin{itemize}

  \item


\end{itemize}

\end{frame}



\begin{frame}{Domains of recursion}

\begin{itemize}

  \item


\end{itemize}

\end{frame}


\begin{frame}{Recursion functions}

\begin{itemize}

  \item


\end{itemize}

\end{frame}


\begin{frame}{Domains of induction}

\begin{itemize}

  \item


\end{itemize}

\end{frame}


\begin{frame}{Induction functions}

\begin{itemize}

  \item


\end{itemize}

\end{frame}



\end{document}
