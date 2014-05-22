---
layout: post
title: "Truth and Deduction"
date: 2014-04-24 10:41:17 +0530
comments: true
categories: 
---

So far we have been working with rules for constructing objects (including types) and seen that these can express a wide range of statements as well as deductions. However, we have not considered the relations of the statements we deduce to those that are _true_. We now turn to such questions. We shall consider these for general deductive systems, and then focus on first-order logic, where there are nice answers to such questions.

##Deductive Systems:

A _deductive system_ is a mechanical system for generating _true_ statement. It consists of axioms - statements that are given to be true, and rules for inference, letting us deduce statements from others. Here _statements_ are mathematical expressions that are either true or false.

In the deductive system we have seen so far, statements correspond to types, with statements true if there is a term (object) of that type. The rules of deduction are the rules for constructing new objects. Unfortunately, some the properties we desire of deductive systems are either not true or unknown for this system.

The best behave deductive system is that of _predicate calculus_, also known as _first order logic_. We shall study this in more detail. But first we consider some general (desired) features of deductive systems.

##Interpretations, Models, Consequences

Typically, statements and other expressions we consider depend on certain constants. An _interpretation_ associates to these constants mathematical objects. The truth of a statement depends on the interpretation.

Given a collection of axioms, an interpretation where these are all true is called a _model_. A statement is a _consequence_ of the given axiom if it is true in all models for the axioms.

The rules of inference form a mechanical system for generating consequences of axioms.

##Soundness 

The most crucial property of the rules of inference is that all statements we deduce are true, or more generally consequences of our axioms. 

##Consistency

A deductive system is consistent if it does not generate both a statement and its negation. If we are working with sound rules of inference, this is a property of our system of axioms.

##Completeness

The rules of inference of a deduction system is complete if we can deduce all the consequences of our axioms using the rules of inference. A landmark result of Godel was his completeness theorem, asserting that first-order logic is complete.

A deduction theorem for arithmetic (or, for example, Euclidean geometry) is complete if it generates all the true statements concerning natural numbers and their usual operations. The famous Godel incompleteness theorem asserts that there is no consistent and complete deduction system for natural numbers.