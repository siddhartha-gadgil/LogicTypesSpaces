---
layout: post
title: "Foundations: Mathematical objects, Types, Rules"
date: 2015-01-06 09:25:57 +0530
comments: true
categories:
---

Quoth Andrej Bauer:

> Mathematicians like to imagine that their papers could in principle be formalized in set theory. This gives them a feeling of security, not unlike the one experienced by a devout man entering a venerable cathedral. It is a form of faith professed by logicians. Homotopy Type Theory is an alternative foundation to set theory.

We now turn to the basics of homotopy type theory. We begin by laying out the basic rules governing such foundations.

We regard almost everything in mathematics as an object - not just numbers or groups, but even theorems, proofs, axioms, constructions etc.  This lets us consider functions acting on, and collections of, just about everything. Formally objects are called _terms_, based on standard terminology of logic, but it is best to think of _term_ as a synonym for _mathematical object_.

Every term has a type, which is generally (but not always) unique. Types themselves are terms, so in particular have types. A type whose objects are themselves types is called a universe. Every set is a type, but not all types are sets.

Our foundations are governed by rules telling us the ways in which we can construct terms, which we will see as we go on. Further, we have rules letting us make two types of judgements:

* that an object $x$ has a type $T$ (denoted $x : T$).
* that two objects $x$ and $y$ are equal by definition.

Objects may be equal even if they are not so by definition. For instance, for a real number x, we have the equality

$$sin^2(x) + cos^2(x) =1$$

which it would be silly to say is true by definition. Rather, it is a proposition that it is true, and we say the two sides of these are propositionally equal (but not definitionally or judgementally equal). Similar considerations also apply to objects having specified types.

In addition to constructing objects by our rules, we can introduce objects and make some judgements related to them as axioms. Axioms may of course introduce inconsistencies.

###The Boolean type###

Let us begin constructing some mathematical objects. We shall do this in the language/formal proof system Agda, but I will try to be self-contained.

We start with a built in universe called Set - objects having type Set are sets. We shall use the **data** statement to construct the type of Booleans - which is a basic logical type used to represent whether a statement is true or false.

``` haskell The Boolean type
data Bool : Set where
  true   : Bool
  false  : Bool
```

The above code gives the construction of three objects: a type called Bool and two objects true and false that have type Bool. This is a simple rule for constructing a type - give it a name and list objects in it. Such a rule, in both Agda and Homotopy type theory (HoTT) is a special case of a more general rule (for constructing inductive types) which we will see later.

Note that we do not have an explicit rule saying that any term with type Bool is either _true_ or _false_, or even that _true_ and _false_ are not equal. Indeed we will not introduce any such rule; instead rules for constructing objects will implicitly tell us that there are exactly two distinct terms with type Bool, true and false.

###A function###

A central role in type theory is played by function types - one may even say that the principal virtue of type theory is treating functions with the respect they deserve (as any good programming language does), instead of trying to wrap them up as subsets of cartesian products that happen to satisfy some properties. We now define our first function, and our first function type.

Given types A and B, functions from A to B give a type

$$A \to B.$$

We construct the function $not$ from Booleans to Booleans, which is the logical negation.

``` haskell Logical Not function
not : Bool -> Bool
not true = false
not false = true
```

We have defined the function _not_ by giving the values on each Boolean constant, and these values are constants. This is the simplest form of *pattern matching*.

Note that being able to construct such a function means $true$ and $false$ are distinct objects as promised.

###Currying functions###

Let us now turn to functions of two variables. By a trick due to the logician Haskell Curry, we do not have to introduce a new type. Instead, observe that if we have a function $f(x,y)$ of two variables (of types $A$ and $B$, taking values of type $C$), then for fixed $x$ we get a function of $y$ only

$f(x , \\_ ) = y \mapsto f(x,y)$

so $f(x, \\_ )$ has the type of functions from $B$ to $C$. Now viewing $f(x, \\_)$ as a function of $x$, we get the curried form of $f$,

$$x \mapsto (y \mapsto f(x,y))$$

which has type

$$A \to B \to C = A \to (B \to C).$$

We next define the logical _and_ (in its curried form). A convenient Agda feature is that we can define functions so that their arguments can appear in the beginning, end, middle or any other combination, just by putting underscores as placeholders.

``` haskell Logical And function
_&_ : Bool → Bool → Bool
true & true = true
false & _ = false
true & false = false
```

The definition is a small extension of pattern matching we used in defining not. If some argument does not affect the result, we can use an underscore to represent all cases.

###Function application###

So far we have defined functions by defining their values on each constant as a constant. In general we use variables to represent arguments, and the values are built from previously constructed terms and the variables. Here is an example.

``` haskell A function using function application
notnot : Bool -> Bool
notnot x = not (not x)
```

We used a variable for the argument of the function, another generalization of pattern matching. The right hand side was built from previously constructed terms using function application. Namely, a function $f$ from $A$ to $B$ can be applied to an object with type $A$ to get an object $f(a)$ with type $B$.

###Lambda: Expressions giving functions

Functions can be specified by describing the image of each argument. These are given by λ-expressions, following the notation of Church's λ-calculus. We define such a function, $verytrue$, below, by equating it with an anonymous function that forms the right hand side.

``` haskell A function using lambda
verytrue : Bool → Bool
verytrue = λ x → x & x
```

We can define (curried) functions of more than one variable using λ-expressions without having to explicitly nest λs.

``` haskell Logical "exclusive or" : nested lambdas
_xor_ : Bool → Bool → Bool
_xor_ = λ x y → (x & (not y)) || ((not x) & y)
```

We have now seen the most basic constructions of types and mathematical terms. We shall next turn to the more powerful constructions - inductive types and dependent types.

## Exercise:
Complete the following three definitions of the logical _nand_ function (look up definition if it is not familiar). Note that subscripts in Agda are obtained by typing, for example, **nand\\\_0**

``` haskell
nand₀ : Bool → Bool → Bool
nand₀ x y =

nand₁ : Bool → Bool → Bool
nand₁ true true =  

nand₂ : Bool → Bool → Bool
nand₂ = λ x y →
```
