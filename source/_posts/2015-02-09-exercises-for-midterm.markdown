---
layout: post
title: "Exercises for midterm"
date: 2015-02-09 10:04:45 +0530
comments: true
categories: Exercises
---

These exercises are for review before the midterm. They are not to be submitted.

1. Let $\\\_\le\\\_$ denote the type family corresponding to the _less than or equal to_ relation. For a function $f : \mathbb{N} \to \mathbb{N}$, what does the type $\Pi\_{n : \mathbb{N}}\Pi_\{m : \mathbb{N}} (m \le n \to f(n) \le f(m))$ represent?

2. For fixed types $A$ and $B$, recall that $A \times B$ is an inductive type. For a type $W$, what is the type of $rec\_{A \times B, X}$? Relate this to Currying functions.

3. For a function $f : \mathbb{N} \to \mathbb{N}$, define a type corresponding to $f$ being bounded (above), using the type family $\\\_\le\\\_$.

4. Let $S$ be a type. Define an inductive type $W(S)$ whose terms are words, i.e., finite sequences, with each letter an element of $S$ or the formal inverse of an element of $S$. For example, if $S$ is the set (which we view as a type) $S = \\{a, b\\}$, then a term of $W(S)$ is $ab\bar{a}a\bar{b}$.
