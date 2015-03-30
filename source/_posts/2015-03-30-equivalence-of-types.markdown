---
layout: post
title: "Equivalence of Types"
date: 2015-03-30 17:03:22 +0530
comments: true
categories:
---

We have seen that functions should be regarded as equal if they are _homotopic_. As usual in mathematics, we have a corresponding notion of equivalence between types, namely a function $f: A \to B$ is an equivalence if there is an inverse functions with compositions equal, i.e., homotopic, to the identity. However, if we naturally turn this into a type, the result (as we see below) is not well-behaved. So we call this relation _quasi-equivalence_.

```haskell
isQuasiEquiv : {X Y : Type} → (X → Y) → Type
isQuasiEquiv {X} {Y} f = Σ (Y → X) (λ g → ((f ∘ g) ∼ (id Y)) × ((g ∘ f) ∼ (id X)))
```

Instead, we define $f$ to be an equivalence if it has separate left and right equivalences. As we see in Algebra, this is an equivalent condition. However, this is better behaved in that the proofs of the proposition as types is generally unique in this formulation.

```haskell
isEquiv : {X Y : Type} → (X → Y) → Type
isEquiv {X} {Y} f = Σ (Y → X) (λ h → Σ (Y → X) (λ g → ((f ∘ g) ∼ (id Y)) × ((h ∘ f) ∼ (id X))))
```
## Exercise: Construct a function from $isEquiv(f)$ to $isQuasiEquiv(f)$.

## An Equivalence

The function $not: Bool \to Bool$ is an equivalence, with itself as an inverse.

```haskell
notnot~id : (not ∘ not) ~ (id Bool)
notnot~id true = refl true
notnot~id false = refl false

notIsEquiv : isEquiv(not)
notIsEquiv = [ not , [ not ,  [ notnot~id , notnot~id ]  ] ]
```


## Monodromy for Quasi-Equivalences

We now see the subtle problem in using the relation that we called quasi-equivalence. Consider the identity map on a type $A$. Let $g$ be an inverse of the identity, so that both conditions become $g \sim id$. However elements of the type are in general two proofs of $g \sim id$. For $a : A$, these are two paths from $a$ to $g(a)$. Combining these we get a path from $a$ to itself, the _monodromy_. In type theoretic terms, this is the following.

```haskell
QImonodromy : (X : Type) → isQuasiEquiv (id X)  → ((x : X) → (x == x))
QImonodromy X qe x = (sym ((p₁ (proj₂ qe)) x)) && p₂ (proj₂ qe) x
```

Thus, for a point $a : A$, an element of $isQuasiEquiv(A)$ gives an element of $a = a$, i.e., a loop. If there are non-trivial loops in $A$, we have more than one proof that identity is an equivalence.
