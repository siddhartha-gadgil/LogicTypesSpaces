\documentclass[10 pt.,handout]{beamer}

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



We look at our foundations. This is a literate agda document.


\begin{code}
module Foundations where

\end{code}



\end{document}
