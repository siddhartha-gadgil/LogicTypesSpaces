---
layout: post
title: "Fun with lists"
date: 2014-03-22 07:39:57 +0530
comments: true
categories: 
---

We shall now return to lists. We have already mapped and flatmapped lists. We shall see how to filter, fold and find, letting us do some actual programming, i.e., with answers that are numbers. We shall also see if-expressions and option types.

###Filtering  and if-then-else###

Let us start with a function checking if a list contains an element with a certain property.

```haskell checking if a list contains an element with a given property
_contains_ : {A : Set} → List A → (A → Bool) → Bool
[] contains _ = false
(x :: xs) contains p = (p x) || (xs contains p)
```


Before turning to filtering, we define an *if expression*, which gives one of two values depending on whether a Boolean term is $true$ or $false$. Note that this is not an if statement, doing something according to a condition, but a function that returns a value depending on the condition.

```haskell if expression
if_then_else : {A : Set} → Bool → A → A  → A
if true then x else _ = x
if false then _ else y = y
```

With this in hand, we define a function filtering elements of a list by a given property. This is defined inductively, using the if expression to decide whether to prepend the first element.

```haskell filtering a list
_filter_ : {A : Set} → List A → (A → Bool) → List A
[] filter _ = []
(x :: xs) filter p = if (p x) then (x :: (xs filter p)) else (xs filter p)
```

###Folding###

So far we have defined many objects and types, but not actually computed anything concrete. To do this, we shall use a very useful function on lists, folding. This is a function that takes as input:

* A list of type $A$, say $[a_0, a_1, \dots, a_n]$.
* An element of type $B$, $b : B$.
* A binary operation that lets us multiply (or add) an element of $A$ to (the left of) an element of $B$, $op : A \to B \to B$.

The fold is obtained by starting with the given element in B, and successively multiplying on the left by elements of the list, starting with the rightmost. This stops when the list is empty, given an element in B. Thus, if we omit parenthesis (assuming associativity of the operation), and if * denotes the operation, then folding is the function

$$fold([a_0, a_1, \dots, a_n], b) = a_0*a_1 * \dots * a_n *b$$

As usual, we define the fold function recursively.

```haskell Folding a list
fold_by_from_ : {A : Set} → {B : Set} → List A → (A → B → B) → B → B
fold [] by _ from b = b
fold (a :: as) by op from b = op a (fold as by op from b)
```

###A program###

Equipped with this, we now give a function computing the sums of squares of numbers from 1 to n. After importing natural numbers, we define (recursively) a function that gives the list of numbers from 1 to n. We then map this to get a list of squares. Finally, we fold this by the addition function to get the sum of squares.

```haskell Sum of squares
open import Nat

upto : ℕ → List ℕ
upto zero = []
upto (succ n) = (upto n) ++ ((succ n) :: [])

listsqs : ℕ → List ℕ
listsqs n = upto n map (λ x → (x * x))

sumsqs : ℕ → ℕ
sumsqs n = fold (listsqs n) by _+_ from zero
```

In the Agda mode of emacs, we can evaluate , for example, the sum of squares up to $20$ to get $2870$. This illustrates that what we are doing does include general purpose programming - indeed it implements an older model of computing, due to Church, which is equivalent to what may be more familiar models.

###Finding and option types.###

We next define a function that finds an element in a list (of type $A$) having a given property. However the list may have no such element, so we cannot always return an object in $A$. Simply giving an error is meaningless mathematically and a bad idea for a program.

To deal with such a situation, we use the type $Option A$, whose objects are $Some a$ for objects $a$ of type $A$, and an object $None$ representing no result.

```haskell Option types
data Option (A : Set) : Set where
  Some : A → Option A
  None : Option A
```

We can now define a find function, returning an option type, containing an object in the list with the given property if there is such an object.

```haskell finding in a list
_find_ : {A : Set} → List A → (A → Bool) → Option A
[] find _ = None
(x :: xs) find p = if (p x) then (Some x) else (xs find p)
```

Thus, using option types, we can represent partially defined functions - those defined on some objects of a type $A$. One often encounters partial functions - finding in a list, taking square-roots, division (avoiding division by $0$), etc.
We can *lift* such a partially defined function to one taking values in an option type. We shall identify partial functions with their lifts.

Suppose we have a partially defined function $f: A\to B$ (not defined on some values of $A$ in general) and a function $g : B \to C$ (defined everywhere). Then it is natural to define the composition of $f$ and $g$ as a partial function defined wherever $f$ is defined. Passing to lifts, this is accomplished by the map function on option types.

```haskell map on an option type
_mapOption_ : {A : Set} → {B : Set} → Option A → (A → B) → Option B
None mapOption _ = None
(Some a) mapOption f = Some (f a)
```

Even better, if both $f: A\to B$ and $g : B\to C$ are both partially defined, we can compose them to get a value in $C$ exactly for elements $a : A$ for which $f(a)$ is defined and lies in the domain of g. We do this  by flatmapping (after passing to lifts once more).

```haskell flatmap on option types
_flatMapOption_ : {A : Set} → {B : Set} → Option A → (A →  Option B) → Option B
None flatMapOption _ = None
(Some a) flatMapOption f = f a
```

There are some obvious common features between lists and option types.

* They are both parametrized by a single type A.
* The type A itself can be embedded in these: map $a$ to the list $a :: []$ in $List\ A$ and the object $Some\ a$ in $Option\ A$, respectively.
* We can map elements of these types, given a function with domain $A$.
* Given a function with domain $A$ and codomain of the form $List\ B$ or $Option\ B$ as appropriate, we can flatmap to get an object of type $List\ C$ or $Option\ C$, respectively.

Types that have these properties (and some consistency relations between the embeddings, map and flatmap) are called Monadic. There are many other useful such types, for example $Future A$ is used to represent an object of type $A$ that will be available in the future, for instance after a long computation. We do not have to wait for the computation to be over before saying what to do with the result when available, even if this involves another long computation which will return a result as a Future.