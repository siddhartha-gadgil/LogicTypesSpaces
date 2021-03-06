\documentclass[10 pt.]{beamer}

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

\item There is a sequence of universes, $\U_0$, $\U_1$, $\dots$
    
\item The universe $\U_i$ has type $\U_{i+1}$. 

\item These are cumulative, i.e., if a type $T$ has type $\U_i$, it also has type $\U_{i+1}$.  


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

\item For each type $A : \U$, $List(A)$ is a type inductively defined by its constructors.
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

\item We can view this as a $lambda$-expression with variable $A : \U$, with the right hand side given by the rules for constructing inductive types.

\end{itemize}

\end{frame}




\begin{frame}{Recursion and Induction : a first look}

\begin{itemize}

\item We can define a function on an inductive type $W$ by defining it on each constructor.

\item To define it on a constructor, we give an expression like the right hand side of a $\lambda$-expression, except that if some argument $w$ to the constructor is of type $W$ (or a more general situation we shall see later), then we can use $f(w)$ in forming the right hand side.

\item For instance, for $f: \N \to X$, we can define $f(succ n) = m$, with $m$ a term formed using all the terms in the context, the term $n : \N$ and the term $f(n) : X$. Thus the data giving $f(succ \_)$ is a term of type $\N \to X \to X$, which we apply to $n$ and then $f(n)$.

\item Similarly, for a type $A$, when defining $f : List(A) \to X$, we can define $f(cons(a)(l))$ in terms of $a$, $l$ and $f(l)$. Thus the data giving $f(cons(a)(l))$ is a term of type $A \to List(A) \to X \to X$, which we apply to $a$, then $l$ and finally $f(l)$. 

\item The analogue of recursive definitions for defining dependnet functions are called inductive definitions.

\end{itemize}

\end{frame}

\begin{frame}{Recursion functions}

\begin{itemize}

\item In Homotopy Type Theory, recursive definitions are formalized by giving rules for forming a function $rec_{W, X}$ for an inductive type $W$ and a type $X$, which when applied to the data for recursive definition for each constructor gives a function $W \to X$.

\item We also have identities saying that function built from $rec_{W, X}$, when applied to the data for a constructor, has the appropriate value.

\item For instance, for $W = \N$ and a type $X$, the data for the constructor $0$ is $f(0) : X$, while the data for the constructor $succ$ is $\N \to X \to X$ (as we have seen).

\item Thus, $rec_{\N , X}$ has type $X \to (\N \to X \to X) \to (\N \to X)$.

\item For the constructor applied to $0$, we get the identity $rec_{\N , X}(z)(g)(0) \equiv z$.

\item For a term $n : \N$, the constructor applied to $succ(n)$ gives the identity $rec_{\N , X}(z)(g)(succ(n)) \equiv g(n)(rec_{\N , X}(z)(g)(n))$.

\end{itemize}

\end{frame}


\begin{frame}{Families}

\begin{itemize}

\item For a type $W$, a \emph{family}  of terms of $W$ is one of:
\begin{itemize}
\item a term $w : W$.
\item a function $\varphi : A \to W'$ where, for each $a : A$,  $\varphi(a) : W'$ is a family of terms of $W$.
\item a dependent function $\varphi : \Pi_{a : A} W'(a)$ where, for each $a : A$, $\varphi(a) : W'(a)$ is a family of terms of $W$.
\end{itemize}

\item We shall call the type of a famiy of $W$ a family-type for $W$. Family types are types of the form:
\begin{itemize}
\item $W$.
\item $A \to W'$ where $W'$ is a family-type $W$.
\item $\Pi_{a : A} W'(a)$ where, for each $a : A$, $W'(a)$ is a family-type for $W$.
\end{itemize}

\item We can recursively define a \emph{member of a family}, which is a term of type $W$.

\end{itemize}


\end{frame}

\begin{frame}{Induced functions on families}

\begin{itemize}

\item Suppose $f: W \to X$ is a function, and $\varphi$ is a family of terms of $W$, then we can define $f_*(\varphi)$ as follows.
\begin{itemize}
\item for $\varphi = w$ with $w : W$, $f_*(\varphi) = f(w)$.
\item for $\varphi : A \to W'$ where $W'$ is a family of terms of $W$, define $f_*(\varphi) = (a : A) \mapsto f_*(\varphi(a))$.
\item for $\varphi : \Pi_{a : A} W'(a)$ where, for each $a : A$, $W'(a)$ is a family of terms of $W$, define $f_*(\varphi) = (a : A) \mapsto f_*(\varphi(a))$.
\end{itemize}

\item This gives functions, or dependent functions, on any given family-types.

\item We can use the same definition for dependent functions $f$. 

\item In all cases, the type of the induced function on a family-type $W'$ depends only on the type $F$ of $f$. We denote this $Ind_F W'$

\end{itemize}

\end{frame}


\begin{frame}{Constructor types for an inductive type}

\begin{itemize}

\item The constructors of an inductive type $W$ must (and can) be terms with type $T$ a so-called \emph{Constructor type} for $W$, which is one of the following:
\begin{itemize}
\item $T = W$.
\item $T = A \to T'$, where $T'$ is a constructor-type for $W$ and $A$ is a type can be formed from the terms in the context not including $W$.
\item $T = W \to T'$, $T'$ as above.
\item $T = \Pi_{a : A} T'(a)$, each $T'(a)$ a constructor type for $W$.
\item $T = \Pi_{w : W} T'(w)$, each $T'(w)$ a constructor type for $W$.
\item $T = W' \to T'$, $W'$ a family-type for $W$.
\item $T = \Pi_{w : W'} T'(w)$, $W'$ family-type for $W$.
\end{itemize}

\item We call a term of a constructor type for $W$ a quasi-constructor for $W$.

\end{itemize}

\end{frame}


\begin{frame}{Domains of recursion}

\begin{itemize}

\item We shall associate to any quasi-constructor $\varphi$ for $W$ a type $R_{W, X}(\varphi)$ which we call the domain of recursion. 
\item This can be defined in all cases for the type of $\varphi$. We give only the dependent function cases below.
\begin{itemize}
\item If $\varphi : W$, then $R_{W, X}(\varphi) = X$.
\item If $\varphi : \Pi_{a : A} W$, then $R_{W, X}(\varphi) = \Pi_{a : A} R_{W, X}(\varphi(a))$.
\item If $\varphi : \Pi_{a : A} W$, then $R_{W, X}(\varphi) = \Pi_{w : W} (X \to R_{W, X}(\varphi(a)))$.
\item If $\varphi : \Pi_{a : A} W'$, with $W'$ a family-type for $W$, then $R_{W, X}(\varphi) = \Pi_{w : W'} (Ind_{W \to X}(W') \to R_{W, X}(\varphi(a)))$.
\end{itemize}

\item Domains of Induction are similar.

\item We now see examples.

\end{itemize}

\end{frame}


\begin{frame}{Recursion functions}

\begin{itemize}

\item The types and identities of recursion functions can be built from the domains of recursion of the constructors.

\item Namely, if an inductive type has constructors $g_1$, $g_2$, $\dots$, $g_k$, then $rec_{W, X}$ has type 
$$R_{W, X}(g_1) \to R_{W, X}(g_2) \to \dots \to R_{W, X}(g_n) \to (W \to X).$$

\item We get identities for each constructor recursively.

\end{itemize}

\end{frame}



\begin{frame}{Inductive type families}

\begin{itemize}

\item A type family $\tilde{W}$ is a family of terms of a universe $\U$.

\item We can define constructor types for $\tilde{W}$ analogous to those for a type $W$, except that we replace all instances of $W$ by members of the family $\tilde{W}$.

\item Recursion, induction etc. are similar.

\end{itemize}

\end{frame}



\begin{frame}{Rules for forming terms}

We now can list all the rules for forming terms.

\begin{itemize}

\item Universes: given in advance.

\item Can form function types and $\Pi$-types

\item Can apply (dependent) functions to arguments of the right type.

\item Can define (dependent) functions using $\lambda$-expressions.

\item Can define inductive types and inductive type families by listing constructors, which must be of the appropriate constructor type.

\item For an inductive type $W$ and a type $X$ (or type family on $W$), we have recursion/induction functions.

\item Finally, we can simply introduce a term with a given type as an \emph{axiom}.

\end{itemize}

\end{frame}



\end{document}
