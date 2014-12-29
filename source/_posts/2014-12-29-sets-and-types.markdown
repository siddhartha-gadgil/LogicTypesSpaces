---
layout: post
title: "Sets and Types"
date: 2014-12-29 13:29:36 +0530
comments: true
categories:
---

## Set theory

A _set_ is a collection of objects with no further structure. Thus, the only property (or function) associated with a set $S$ is _membership_ - a different object $x$ may or may not belong to $S$ (denoted as usual $x\in S$).

It is natural to try to reverse this and consider, for any property of objects (for example sets) the set that consists of those satisfying this (for example all sets that have a certain property). Cantor discovered, however, that this leads to paradoxes. For instance, Russell's paradox appears if we consider the set $ S = \\{X : X \notin X\\}.$

We ask whether $S\in S$. By the definition of $S$, if $X\in X$, then $X\notin X$ and vice versa.

To prevent such paradoxes, we cannot allow sets to be defined by arbitrary properties. We do of course see definitions that look very similar to the above in mathematics - these are definitions of _subsets_ of a given set. Indeed one of the valid ways of defining a set is to consider the elements of a given set that satisfy some property.

Clearly defining only subsets of pre-existing sets will not get us far. Instead, set theory is formulated in terms of axioms, many of which assert the existence of various sets. For instance, if $S$ is a set then there is an axiom asserting the existence of the _power set_ of $S$, whose elements are subsets of $S$. Sometimes we need to consider collections, such as that consisting of all groups, that are so large that they cannot be treated as sets but are considered _classes_ instead.

## Foundations using set theory

Sets (and classes) form the objects in the usual foundations of mathematics, analogous to the vocabulary of the language of mathematics. However to describe theorems, proofs, or even properties describing sets, we need rules telling us how to form _terms_ - corresponding to sets that may depend on variables, as well as _formulas_ - corresponding to properties. We also need to specify the rules of deduction by which we can show that a theorem (given by a formula) is true. Standard foundations are the rules of _predicate calculus_.

These foundations can indeed express, or rather encode, all real mathematics. But this encoding is often very much longer than real life mathematics and are also opaque. If one actually expects to fully formalize mathematics, it is better to use some form of _type theory_.

## Type theory

In type theory we replace sets by types, and the notion of membership $x\in S$, $x$ belongs to the set $S$, by having an appropriate type $x : T$, i.e., $x$ has type $T$. The crucial difference is that objects of a given type $T$ (unlike elements of a set $S$) are expected to be of the same nature. For instance, the a typical type is $\mathbb{N}\to \mathbb{N}$, consisting of functions from $\mathbb{N}$ to $\mathbb{N}$.

Thus, for example $f : \mathbb{N}\to \mathbb{N}$ gives a lot of information about $f$. In particular we know that if $a : \mathbb{N}$, it is meaningful to talk of $f(a)$ and that this  is  a natural number too. Typically types allow us to restrict which expressions are meaningful, and infer the type of a meaningful expression. Such information is very useful in programming languages (where it is called type checking) - not only revealing errors without running a program (i.e., at compile time) but allowing a detailed analysis of the program which is used by tools.

In practical programming languages, type checking may be more or less strict - with stricter checking meaning that expressions that can cause error while running being more likely to be rejected at compile time itself. Some languages will treat an expression $f(a)$ as valid as long as $f$ is a function, and only give an error if $a$ has type different from the domain of $f$ when we actually try to compute this expression, while stricter  languages will reject such expression  unless the types match. However in practical code a function $f(x, y) = x/y$ will generally be regarded at best as a function of two real variables, with the compiler not checking that $y$ is non-zero.

There is another more conceptual choice in the form of type theory considered - whether or not to allow sub-typing. For instance, we can either regard every natural number as a rational number, or work with  the canonical inclusion that takes a natural number $n$  to the rational number $n/1$.

## Types as spaces

With  all these choices, type theory  is a very fragmented subject, with both practical engineering considerations and whims dictating the many choices. It is clear to a large extend what behaviour we expect from sets, and this anchors our axiomatization. Traditionally type theory is not constrained in such a manner.

Homotopy type theory is born out of an observed deep connection between (a form of) type theory and topology. Thus behaviour that we  expect from topology guides our  choices, so we can hope for  coherent standard foundations. We shall see that this connection is indeed extremely fruitful. 
