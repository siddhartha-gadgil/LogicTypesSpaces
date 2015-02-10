---
layout: post
title: "Dependent function types: Sections of a bundle"
date: 2015-01-22 17:56:43 +0530
comments: true
categories:
---

## Dependent functions

A function $f$ on a domain $A$ when applied to an elements $a$ of type $A$ gives a value $f(a)$. Further, a function is determined by the values it gives, in the sense that if $f$, $g$ are functions with domain $A$ so that

$$\forall x\in A, f(x) = g(x)$$

then
$$f=g.$$

Dependent functions generalize functions, with the above properties continuing to hold. What we no longer require is that $f(a)$ has a fixed type independent of $a$, namely the codomain B. Instead we have a family of codomains $B(a)$, so that $f(a)$ has type $B(a)$.

Such objects are common in mathematics (and physics). For example, the velocity of water flowing on a sphere  gives a vector field on a sphere. At a point $x$ on the sphere, the value of the vetor field $V$ lies in the tangent space at the point, i.e.,

$$V(x) \in T_x S^2.$$

Hence it is best to view vector fields as dependent functions. In mathematics, the codomains are generally called fibers, which together form a fiber bundle, and dependent functions are called sections of this bundle.

We can (and often do) regard a dependent function as an ordinary function with codomain the union of the various codomains. But, besides losing information, the function we get is not natural, in the sense that it does not respect the underlying symmetries.

## Products and $\Pi$-types

Another situation which is best viewed in terms of dependent functions is a product. Consider a product $A\_1 \times A\_2 \times \dots \times A\_n$. An element of such a product is a tuple $(a_a, a_2, dots, a_n)$. We would like to view such tuples as functions $a$ on the index set $\\\{1, 2, \dots, n\\\}$, but to do so we would have to require $a(i) : A_i$, i.e., a separate codomain for each index. Thus tuples are dependent functions.

More generally, if we have a family of types $B(a)$ indexed by a set $A$, then elements of the product

$$\Pi_{a : A} B(a)$$

are exactly dependent functions $f$ on $A$ so that $f(a)$ has type $B(a)$ for $a : A$. Thus a type of dependent functions is denoted as in $\Pi\_{a : A} B(a)$ and is often called a $\Pi$-type.

## Examples and code

We now turn to some simple examples and code. First we consider type families, which give the collection of codomains for dependent functions. The typical example is vectors of length $n$ of elements of a type $A$. Formally, a type family is just a function with codomain a universe, so the values the function takes are types.

``` haskell The Type family of vectors of length n
data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)
```

This gives a family of types *parametrized* by A and *indexed* by natural numbers. The difference between parameters and indices is a bit subtle but crucial. Observe that the Agda syntax treats them quite differently.

###Inductive types and inductive type families###

We defined Booleans and natural numbers using the data statement, and defined functions on them by pattern matching. More conceptually, these are inductive types, and functions defined on them are defined by applying the recursion function. For instance, in the case of Booleans, the recursion function takes as input a type $A$ and two objects with that type (the values of $true$ and $false$) and gives a function from Booleans to $A$.

In the case of lists, for each type $A$, we obtain a corresponding inductive type. Thus we have a family of inductive types, parametrized by the type $A$.

In the case of vectors too, the type $A$ acts as a parameter.  Assume that the type $A$ is fixed, so vectors are now a family of types indexed by natural numbers.

However, the vectors of a fixed size (say $7$) do not form an inductive type - we cannot define a function recursively on vectors of length $7$ alone.  In this case, this is evident from the definition, as the constructor giving vectors of size $7$ uses vectors of size $6$. So a recursive definition must also involve vectors of size $6$, hence of $5$ etc.

We can, however, recursively define functions on vectors of all sizes, i.e., of all values of the index. For examples, here is the function that appends (adds to the end) an element to a vector.

```haskell Appending to a vector
_:+_ : {A : Set} → {n : ℕ} → A → Vec A n → Vec A (succ n)
a :+ [] = a :: []
a :+ (x :: xs) = x :: (a :+ xs)
```

Thus, vectors form an inductive type family indexed by natural numbers (and parametrized by A). As we remarked, the type for a given index is not an inductive type. Note that even in cases where we can meaningfully write down a recursion rule for the type at a fixed index, such a recursion rule does not hold, i.e., there is no recursion function using which we can translate pattern matching into function applicatio.

**Remark:** From the point of view of programming languages, there is another sense in which indexing by natural numbers is different from parametrizing by types - the types we construct depend on *objects*, not just other types. Modern languages usually allow types to depend on other types (sometimes called generics), but most do not allow dependence on objects.

###A dependent function###

We shall now construct a dependent function _countdown_ that maps a natural number $n$ to the list consisting of natural numbers from $n$ down to $0$. Thus the type of $countdown(n)$ is vectors of natural numbers of length $n+1$.

```haskell countdown : a dependent function
countdown : (n : ℕ) → Vec ℕ (succ n)
countdown zero = zero :: []
countdown (succ m) = (succ m) :: (countdown m)
```

The definition in terms of pattern matching is similar to recursive definitions of functions. In terms of homotopy type theory, dependent functions on inductive types are constructed by applying a dependent function called the *induction function* to the data.

As mentioned earlier, the type of a dependent function is called the *product type* corresponding to the family of types with base the domain. For instance, the type of countdown is

$$\prod\limits_{n : \Bbb{N}} Vec (\Bbb{N}) (n+1).$$

Except for universes (which we will keep in the background as far as possible), we have now seen all the type constructions - inductive types, functions and dependent functions.

## Dependent pairs

Besides dependent products, the other fundamental dependent type associated to a type $A$ and a family of types $B: A \to \mathcal{U}$ is the _dependent sum type_, denoted $\Sigma\_{a : A} B(a)$, whose elements are pairs $(a, b)$ with $a : A$ and $b : B(a)$. Like the pair type $A \times B$, this can be defined as an inductive type.

``` haskell
data Σ (A : Type) (B : A → Type) : Type where
  [_,_] : (a : A) → (B a) → Σ A B
```

###Type checking with dependent types###

A principal use of types in programming is to avoid writing meaningless expressions, by ensuring that such expressions violate the rules for constructing objects and types. Dependent types are even better than this. For instance, consider the _zip_ operation on vectors which associates to a vector of type $A$ with entries $a\_i$ and a vector of type $B$ with entries $b\_j$ a vector of type $A\times B$ with entries pairs $(a\_i, b\_i)$. This makes sense only when both vectors have the same length. Using dependent functions and types, we can define the function in such a way that it is defined only on pairs of vectors with the same length.

```haskell Componentwise operation on vectors
zip : {A : Set} → {n : ℕ} → Vec A n → Vec A n → Vec A n
zip  [] [] _ = []
zip  (x :: xs) (y :: ys)  = [x, y] :: (zip  xs ys)
```

Note that we could have used lists in place of vectors, but we would then have to give a definition that can lead to errors at runtime, or truncates perhaps giving unexpected values.

## Exercise:

* Define a function $vmap$ on vectors analogous to $map$ on lists.
