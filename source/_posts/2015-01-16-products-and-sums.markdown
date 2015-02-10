---
layout: post
title: "Products and Sums"
date: 2015-01-16 16:22:28 +0530
comments: true
categories:
---

Given types $A$ and $B$, we can combine them to get the product types $A\times B$ and the sum type $A \oplus B$. These are both inductive types parametrized by $A$ and $B$.

## The Product

A term in the product $A \times B$ corresponds to an element of $A$ and an element of $B$. Hence we can define the product using a single constructor. We use square brackets for pairs as parenthesis have other meanings in Agda.

```haskell
data _×_ (A B : Set) : Set where
  [_,_] : A → B → A × B
```

## The (direct) Sum

The direct sum $A \oplus B$ of types $A$ and $B$ can be thought of as the type whose elements are the elements of $A$ and the elements of $B$. Formally we have inclusion maps $\iota\_j$ from the given types. Hence we get a description with two constructors.

```haskell
data _⊕_ (A B : Set) : Set where
  ι₁ : A → A ⊕ B
  ι₂ : B → A ⊕ B
```
