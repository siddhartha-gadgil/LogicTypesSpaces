---
layout: post
title: "Inductive types: Natural numbers, Lists"
date: 2015-01-08 09:03:29 +0530
comments: true
categories:
---

Booleans were a finite type, where we specified all constant objects of the type. More generally, we can construct inductive types by introducing constructors - functions mapping to the type. For instance, we can define the natural numbers (which in logic generally start with $0$).

``` haskell Natural Numbers: Inductive Definition
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ
```

Here $zero$ is $0$ and $succ$ is the function taking any natural number to its successor. Any natural number can be built from these, and different expressions give different numbers. However, as with the case of Booleans, we do not have any explicit rules giving such statements  - indeed, it would be quite painful to formulate such rules, as we have to define expressions, equality of expressions etc. Instead, the rules for defining functions from natural numbers implicitly contain such statements. We define functions on natural numbers by pattern matching, but this time the patterns can involve the constructors.

``` haskell Addition of natural numbers
_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ m) + n = succ (m + n)
```

The left hand sides pattern match on the constructors for natural numbers. Notice that this is a recursive definition, the right hand side in the second pattern for defining addition also involves addition. This is fine as the definition lets us rewrite a sum in terms of sums of simpler terms, and such a process eventually terminates. However, we can write nonsensical definitions in general.

```haskell Recursion resulting in infinite loops
forever : ℕ → ℕ
forever zero = zero
forever (succ n) = forever (succ (succ n))
```

When we try to compute $forever(1)$ (where $1 = succ (zero)\$), we get that $forever(1) = forever(2)$, and this continues forever. Fortunately, Agda will not let us make such definitions. This does come at a price though - sometimes it takes a lot of work to convince Agda that functions terminate. There are deeper, conceptual limitations to any system ensuring termination, as discovered by Turing, which we return to in the future.

In homotopy type theory, the rules for such recursive definitions are nicely formulated so we cannot making nonsensical definitions. We shall see how this is done much later. We now define a couple of other recursive functions.

```haskell Multiplication of natural numbers
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)
```

```haskell Factorials
factorial : ℕ → ℕ
factorial zero = succ zero
factorial (succ n) = (succ n) * (factorial n)
```


Our constructors are unfortunately only as efficient as tally marks in dealing with actual numbers. Agda has a built in type that lets us deal with natural numbers the usual way. We can invoke it as below.

```haskell Agda: Builtin natural numbers
{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}
```

**Note**:  If you are using the latest version of Agda (2.4.2.2),  it is enough to include this line `{-# BUILTIN NATURAL ℕ #-}`  

### Exercise

Complete the following definitions of the square of a natural number, using the addition but **not** the multiplication of natural numbers.

```haskell
sq₀ : ℕ → ℕ
sq₀ zero =
sq₀ (succ n) =
```

Complete the following definitions of the square of a natural number. You may use the addition and multiplication of natural numbers.

```
sq₁ : ℕ → ℕ
sq₁ = λ n →
```


#Lists : A parametrized type###

We shall now define the type of Lists of objects, each of which is of a given type A. Thus, we are defining not just one type, but a family of types parametrized by the type A.

```haskell Lists
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A
```

The constructor $[]$ is just a constant, giving us the empty list. The constructor $ \\_ :: \\_ $ gives a list from an element $a$ in $A$ and a list $l$ of elements in $A$ by adding $a$ to the beginning of the list $l$. For instance (after importing the natural numbers constructed earlier) we can describe the list [1, 2, 3] as

```haskell The list [1, 2, 3]
open import Nat

onetwothree : List ℕ
onetwothree = 1 :: (2 :: (3 :: []))
```

We can make things a little cleaner by specifying that $\\_::\\_$ is right associative. We shall discuss this later. Let us now define the length of a list. Here is our first definition.

```haskell Length of a list: First attempt
length₀ : (A : Set) → List A → ℕ
length₀ _ [] = zero
length₀ A (a :: l) = succ (length₀ A l)
```

We have given a recursive definition. We defined a function of the type $A$ as well as the list, as we needed $A$ in the right hand side of the second pattern. But $A$ can be inferred in this pattern - it is the type of the element $a$. So we can declare $A$ to be an optional argument (by putting it in braces), and let Agda infer its value. This gives us a cleaner definition.

```haskell Length of a list
length : {A : Set} → List A → ℕ
length [] = zero
length (a :: l) = succ (length l)
```

Next, we define some functions recursively. The first is concatentation, which combines two lists by giving the entries of the first followed by those of the second.

``` haskell Concatenation of Lists
_++_ : {A : Set} → List A → List A → List A
[] ++ l = l
(a :: xs) ++ l = a :: (xs ++ l)
```

We next define the function that reverses a list.

```haskell Reversing a list
reverse : {A : Set} → List A → List A
reverse [] = []
reverse (a :: l) = (reverse l) ++ (a :: [])
```

We now turn to some more interesting functions. Given a list of objects of type $A$ and a function $f:A \to B$, we can apply $f$ to each entry of the list to get a list of elements of $B$. This is usually called the $map$ function.

``` haskell map function on lists
_map_ : {A B : Set} → List A → (A → B) → List B
[] map _ = []
(a :: xs) map f = (f a) :: (xs map f)
```

We can do more - if we have a function $f: A \to List\\ B$, then we can map a list $l$ of elements of $A$ to a list of elements of $B$ - each element of $l$ maps to a list of elements of $B$, and we get a list by concatenating these lists together.

``` haskell flatmap on lists
_flatMap_ : {A B : Set} → List A → (A → List B) → List B
[] flatMap _ = []
(a :: xs) flatMap f = (f a) ++ (xs flatMap f)
```

In case you did not notice, we have been programming in a functional language. To those used to imperative languages (say C), this may not look like programming, but programming in functional languages is essentially building functions, collections and structures. Indeed anyone who has programmed in (for example) scala for a while hungers for a flatmap function. We will next see some of the other main ingredients of collections in functional languages - finding in, filtering and folding lists. 


### Exercises

* Define a function **fill** which, given a type $A$ (implicitly), an element $a : A$ and a natural number $n$, gives a list of length $n$ all of whose entries are $a$.
* Define a Boolean valued function **empty** on lists giving whether a list is empty.
