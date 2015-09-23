---
layout: post
title: "Homotopy Type theory"
date: 2015-03-30 12:58:54 +0530
comments: true
categories:
---

In _homotopy type theory_ , we interpret a type $A$ as a space $\|A\|$, and a term $a : A$ as a point $\|a\| \in \|A\|$ in the corresponding space. Here space means topological space, but we  do not actually need to know what  this means. All we need of  spaces is:

* Subsets of a Euclidean space are spaces.
* For spaces $X$ and $Y$, it is meaningful to talk about continuous functions between them.
* For spaces  $X$ and $Y$, continuous functions between $X$ and $Y$ also form a space $C(X, Y)$.
* Currying and uncurrying are continuous.

## The interpretation.

As mentioned above types and terms are interpreted as spaces and points. For types $A$ and $B$, we interpret $A \to B$ as the space of continuous functions $C(\|A\|, \|B\|)$. We can similarly interpret dependent functions, but we shall not go into  details here.

The most crucial ingredient in our interpretation is that of an equality type. For $x, y : A$, the type $x = y$ is interpreted as the space of _paths_ in $\|A\|$ from $\|x\|$ to $\|y\|$, i.e., the space of continuous functions $\alpha: [0, 1] \to \|A\|$ so that $\alpha(0) = \|x\|$ and $\alpha(1) = \|y\|$.

It is a result of Voevodsky and Awodey-Warren that we do have a consistent interpretation of type theory, in the sense we have seen it so far, in which types, terms, (dependent) function types and equality types are mapped in the above fashion.

Given such an interpretation, various topological notions can be defined purely in type theoretic terms. The first of these arises when we ask  when functions are equality.

## Equality of functions.

Let $A, B$ be types and $f, g: A \to B$ be functions. Then $f$ and $g$ must be equal if and only if there is  a path between $\|f\|$ and $\|g\|$ in $C(\|A\|, \|B\|)$. Such a path is a function $[0, 1] \to \|A\| \to \|B\|$, which after Uncurrying corresponds to a function $([0, 1] \times \|A\|) \to \|B\|$. Flipping the coordinates in the domain and Currying gives a function $\|A\| \to ([0, 1] \to \|B\|)$, i.e., a function mapping points of $\|A\|$ to paths in $\|B\|$. Indeed, using that the path we started with is from $\|f\|$ to $\|g\|$, it is  easy to deduce that a point $\|a\|$ is mapped to a path from $\|f(a)\|$ to $\|g(a)\|$. Such a path corresponds to a term of the type $f(a) = g(a)$!

Thus, we see that  if we have a consistent homotopical interpretation, then the equality type $f = g$ must equal the type
$$\Pi_{a : A} (f(a) = g(a)).$$

Function extensionality was the postulate that these types  were equal. We shall not postulate this, but instead introduce  and study _homotopy_ type $f\sim g$ corresponding to such equality. We see this  in Agda code. Firstly, we see the definitions for functions and dependent functions.

```haskell
_∼_ : {X Y : Type} → (f g : X → Y) → Type
_∼_ {X} {_} f g = (x : X) → (f(x) == g(x))

_~_ : {X : Type} → {Y : X → Type} → (f g : ((x : X) → (Y x))) → Type
_~_ {X} {_} f g = (x : X) → (f(x) == g(x))
```

It is easy to see that this gives an equivalence relation.

```haskell
rfl : {X Y : Type} → (f : X → Y) → (f ∼ f)
rfl {X} {_} f = λ x → (refl (f x))

symm : {X Y : Type} → (f g : X → Y) → (f ∼ g) → (g ∼ f)
symm {X} {_} f g pf = λ x → (sym (pf x))

_trans_ : {X Y : Type} → (f g h : X → Y) → (f ∼ g) → (g ∼ h) → (f ∼ h)
_trans_ {X} {_} f g h f∼g g∼h = λ x → (f∼g x) && (g∼h x)
```

While these are simple inductive constructions, in topological terms they are more interesting. Given paths $\alpha, \beta: [0, 1] \to X$, for a space $X$, if $\alpha(1) = \beta(0)$ we can define a path $\alpha * \beta$ which is the  path $\alpha$ followed by the path $\beta$. This is the path corresponding to transitivity. Reflexivity corresponds to constant paths. Finally symmetry corresponds to the map associating to a path $\alpha$ the path $\bar{\alpha}: t \mapsto \alpha(1-t)$.
