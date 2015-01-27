---
layout: post
title: "Rooted trees and General induction"
date: 2015-01-25 09:36:02 +0530
comments: true
categories:
---

We now consider a more complex example, which illustrates the most general form of constructors for inductive types.

A rooted tree with leaf labels of type $A$ is a structure built recursively, being of one of the forms:

* a single vertex, which is the root, with a label from $A$, or
* a vertex, the root, to which are attached finitely many rooted trees with leaf labels by an edge to their roots.

To model this, specifically to model "finitely many rooted trees", we introduce the inductive type family associating to a natural number $n: \mathbb{N}$ the set of natural numbers less than $n$.

## The Fin type family.

We construct an inductive type family $Fin: \mathbb{N} \to \mathcal{U}$, with $Fin(n)$ consisting of integers $k$ with $0 \leq k < n$. For $n >0$, this has an element $0$. Further, if $k$ gives an element of $Fin(n)$, then $k + 1$ is an element of $Fin(n +1)$. It is easy to see that these give the constructors of the type family. Thus,

```haskell
data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)
```

## Inductive family for rooted trees.

Observe that for $n : \mathbb{N}$, a collection of $n$ objects of type $X$ can be viewed as a function $Fin(n) \to X$. To consider all finite trees we consider terms of type $\Pi\_{n : \mathbb{N}} Fin(n)\to X$. Using this, we can define the inductive type of rooted trees with leaf labels of type $A$.

```haskell
data RootedTree (A : Type) : Type where
  leaf : A → RootedTree A
  node : (n : ℕ) → (Fin(n) → RootedTree A) → RootedTree A
```

## Constructors, Recursion and Induction generalized

Note that the constructor for rooted trees is not of the earlier forms, but a more general form. For a type $W$, we can regard a term of $A \to W$ as giving a family of terms of $W$, indexed by $A$. More generally, we can construct families by regarding $W$ itself as the type of a family, and regarding functions, and dependent functions, to families of terms of $W$ as families of terms of $W$. Note that the domains cannot involve $W$.

We add another rule for types of constructors for $W$. This completes our list of constructors, so we now have the full definition of inductive types.

* If $T$ is the type of a constructor of $W$, and $V = \dots \to W$ is the type of a family of terms of $W$, then $V \to W$ can be the type of a constructor.

Consider recursive and inductive definitions on rooted trees, or more generally inductive types with constructors including the new type. The value of a function on a node can depend on values on each of the rooted trees that constitute it. To formalize this, observe that if $\alpha: A \to W$ is a family of terms of type $W$, and $f : W\to X$, then we obtain a function $f \circ \alpha: A \to X$ by composition. The value of $f$ on the image of the constructor can depend on $F \circ \varphi$.

We thus make the following rule for $R\_{W, X}$, which is easy to generalize to arbitrary families and to induction functions.

* If $T$ is the type of a constructor of of $W$, $A$ is a type and $\alpha : A \to W$ is a variable (or term), then for a constructor $\varphi : (A \to W) \to T$, we have $R\_{W, X}(\varphi) = (A \to W) \to (A \to X) \to R\_{W, X}(\varphi(\alpha))$.

## Exercise:

* Define a fold function, which, given $n : \mathbb{N}$ (which can be inferred), $f: Fin(n) \to A$ and $\\_ *\\_ : A \times B \to B$, for types $A$ and $B$, has result
$f(0) * (f(1) * (\dots * (f(n-1) * b)))$

* Define a function that, given a rooted tree with leaf labels in $A$ gives the list of labels.
