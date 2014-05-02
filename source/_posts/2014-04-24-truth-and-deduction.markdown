---
layout: post
title: "Truth and Deduction"
date: 2014-04-24 10:41:17 +0530
comments: true
categories: 
---

# Truth and Deduction

So far we have been working with rules for constructing objects (including types) and seen that these can express a wide range of statements as well as deductions. However, we have not considered the relations of the statements we deduce to those that are _true_. We now turn to such questions. We shall consider these for general logical systems, and then focus on first-order logic, where there are nice answers to such questions.


##Logical Systems:
We begin with some generalities concerning logical systems. 

* A logical system is based on a _formal language_, which specifies a set of (well-formed) expressions of various kinds.
* The language typically involves various types of _constants_. 
* An _interpretation_ associates to constants concrete mathematical objects. The logical system specifies what are valid interpretations.
* There is a specified class of expressions, called _statements_, which, for a given interpretation, are unambiguously either true or false. Note that we do not mean that there is an algorithm to decide whether a given statement is true or false.
* Given a collection of statements, our _assumptions_, the _rules of deduction_ specify a collection of statements, which we say can be _deduced_ from the assumptions. 

### Desired properties of logical systems:

Suppose we have a logical system. For any sane person to accept it, it must at least be __sound__, in the following sense:

####Soundness:

A logical system is sound if, given a set of assumptions, and an interpretation in which all our assumptions are true, then all the statements that we deduce from our assumptions are also true.

####Completeness of  a logical system:

Suppose we fix our assumptions - a collection of statements. We say that a statement $P$ is a _consequence_ of these assumptions if, for every interpretation in which our assumptions are true, the statement $P$ is true.

A logical system is _complete_ if every statement that is a consequence of a collection of assumptions can be deduced from these.

## Axiomatisation

Suppose we are given a mathematical object, such as the natural numbers (or the Euclidean plane). Then an _axiomatisation_ is a formal system of rules that generates statements about the object under consideration so that

* Every statement generated is true.
* All true statements are generated.

We can give an axiomatisation by specifying:

* A logical system
* A collection of assumptions (axioms).