---
layout: post
title: "types and first-order languages"
date: 2015-01-04 13:25:39 +0530
comments: true
categories:
---

## Grammar

A first-order languages has words and phrases (expressions) belonging to four types/type families.

* term
* formula
* function - determined by degree
* predicate - determined by degree.

Note that the last two types can only have words as members, i.e., we cannot create elements of these types. So for a fixed language, there are only a fixed number of types. Usually functions and predicates have degrees $1$ or $2$, so there are only about $6$ types of expressions.

## Formation rules.

The formation rule for new phrases are entirely in terms of the types of its constituent words/phrases, and there are typically only about $6$ such types. This means the language is not very _expressive_.

## Consequences of low expressiveness

Depending on ones objective, there are two ways to cope with lack of expressiveness.

* In _weakly typed_ or _dynamically typed_ programming languages, a lot of expressions are permitted (at compile time, or even run time) but lead to errors.
* In mathematics, one embeds actually mathematics in the not very expressive language of set theory paying the price of being verbose and opaque.
