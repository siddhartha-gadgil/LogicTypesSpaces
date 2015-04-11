---
layout: post
title: "Logic from Types"
date: 2015-02-02 06:46:59 +0530
comments: true
categories:
---

At the core of homotopy type theory (and its predecessors) is the idea of *propostions as types*. Namely, we interpret logical _propositions_ - statements that are either true or false, as _types_, with a _term_ having a given type being viewed as a _proof_ of the corresponding proposition. The Curry-Howard correspondence lets us embed all of logic into type theory in the manner.

###True and False###

We begin by representing the two simplest propositions: true - always true,  and false.

```haskell True and False types
data True : Type where
  qed : True


data False : Type where

```

The $True$ type has just one constructor, giving an object with type $True$. On the other hand, the $False$ type has no constructors, so there are no objects of type $False$.

There are various ways of building propositions from other propositions. We see how these translate to constructions of types.

###Logical implies###

If $P$ and $Q$ are propositions, which we identify with their corresponding types. We interpret the proposition $P \implies Q$ as the function type $P \to Q$.

###Some deductions###

*Modus Ponens* is the rule of deduction (going back to antiquity) that says that if the proposition $P$ is true, and $P$ implies $Q$, then $Q$ is true. We can prove this in the types interpretation. Namely, Modus Ponens translates to the statement that if we have an objects of type $P$ and $P \to Q$, then we have an object of type $Q$. We get an object of type $Q$ by function application.

```haskell
mp : {P : Type} → {Q : Type} → P → (P → Q) → Q
mp p imp = imp p
```

Next, we see my favourite method of proof - vacuous implication. This says that a false statement implies everything, i.e., for any proposition $P$, we have $False \implies P$, which in type theory says $False\to P$ has objects.

As the $False$ type has no cases at all, a function is defined on $False$ by using an absurd pattern, which just says that there are no cases, so no definition is needed.

```haskell
vacuous : {A : Type} → False → A
vacuous ()
```

Formally, as the $False$ type has no constructors, the recursion function $rec\_{False, A}$ has type $False \to A$. We simply take this as the vacuous implication.


###Even and Odd numbers###

Next, we define a type family $Even(n)$, for $n : \mathbb{N}$, which is non-empty if and only if $n$ is even. To do this, we see that a number is even if and only if it is even as a consequence of the rules

* $0$ is even.
* If $n$ is even, so is $n + 2$.

Thus, we can define the inductive type family:

```haskell
data Even : ℕ → Type where
  0even : Even 0
  _+2even : {n : ℕ} → Even n → Even (succ (succ n))
```

We can prove that $4$ is even by applying the second constructor to the first constructor (telling us that $0$ is even) twice.

```haskell
4even = (0even +2even) +2even
```

We next show that $1$ is odd. This means that we have to show that the type $Even\\ 1$ is empty. While rules let us construct objects, and verify their types, there is no rule that tells us directly that a type is empty.

However, there is a nice way of capturing that a type $A$ is empty - if there is a function from $A$ to the empty type $False$, then $A$ must be empty - there is nowhere for an object of type $A$ to be mapped.

Indeed, what we prove is that there is a function from $Even\ 1$ to $False$ ; we define this using an absurd pattern.

```haskell 1 is odd
1odd : Even 1 → False
1odd ()
```

This can be formalized by defining a dependent function on the inductive type family $Even$ with appropriate type.

### More types for propositions###

We now see the types corresponding to other ways of combining propositions: logical operations _and_ and _or_.

Firstly, if $A$ and $B$ are types corresponding to propositions, then there are objects with each of these types if and only if there is a pair $(a, b)$ of the pair type $A \times B$.

Next, suppose $A$ and $B$ are types corresponding to propositions and we wish to construct a type corresponding to $A$ *or* $B$, then we require a type whose elements are elements of $A$ and elements of $B$, or more accurately the images of such elements under constructors. This is the direct sum type.


The above methods let us combine propositions without quantifiers in all the logical ways. In doing so we used type theory, but not dependent types. Dependent types also let us express logical statements with quantifiers.

###For all

Suppose we have a type $A$ and a family of types $P(a)$ (which we regard as propositions), with a type associated to each object $a$ of type $A$. Then all the types $P(a)$ have objects  (i.e., all corresponding propositions are true) if and only if there is a dependent function mapping each object $a$ of type $A$ to an object of type  $P(a)$. Thus, the logical statement

$$\forall a \in A\ P(a)$$

translates to the product type

$$\prod\limits_{a : A} P(a).$$

As we have seen, in Agda we represent the product type as $(a : A) \to P(a)$

###Exists

Next, if we are given a collection of types $B(a)$ for objects $a$ of type $A$, the type corresponding to at least one of these types having an element is a $\Sigma$-type, as there is an element of $B(a)$ for at least one $a : A$ if and only if there is a pair term $(a, b)$ with $b : B(a)$.

## A proof by induction

If $n$ is a natural number, we can prove by induction that one of $n$ and $n+1$ is even. We shall prove this in its  type theoretic form. We will do this in an Agda module to keep notation clean - the module consists of all the tab spaced lines following its definition. In the following code, we define the property that for all $n$, one of $n$ and $n+1$ is even as $P$ (in a submodule). We then prove the induction step and use  it to prove  the  theorem.


```haskell
module n|n+1even where
  P : ℕ → Type
  P n = (Even n) ⊕ (Even (succ n))

  step : {n : ℕ} → P n → P (succ n)
  step (ι₁ p) = ι₂(p +2even)
  step (ι₂ p) = ι₁ p

  thm : (n : ℕ) → P n
  thm 0 = ι₁ 0even
  thm (succ n) = step (thm n)
```

The definition is just a translation of the logical or into dependent sums and of $\forall$ into dependent functions.

In the induction step, we assume that we have a proof for $n$. Thus $n$ and the corresponding proof are arguments, but $n$ can be inferred. There are two cases - if we have a proof that $n$ is even (i.e., the first alternative  for $P(n)$), we obtain a proof that $n+2 = (n+1) + 1$ is even by using the  rule $\\_+2even$, which is the second alternative for the statement $P(n+1)$. In the case where  $n + 1$ is  even, we directly obtain the first  alternative for $P(n+1)$.

The theorem itself is simply obtained by putting together the base case and the induction step.

This proof is remarkable in many ways. First of all, note that this is no longer or more complicated than an informal proof. Further, note that we did not have to invoke the usual induction axiom schema, but instead just used the rules for constructing objects. Most significantly, as most of our types are inductive type (or type families), we get recursive definitions and inductive proofs in all these cases.

Indeed,  using recursive definitions for inductive types we get all so called *universal properties*. Furthermore, traditionally universal properties require a separate uniqueness statement. But recursion-induction is powerful enough to even give the uniqueness statements for universal properties. This means a great deal of mathematical sophistication (universal algebra, various aspects of category theory) are encapsulated in these simple functions.

## Functions with conditions and certificates.

Often functions are meant to be defined only when some conditions are satisfied, for instance we may  wish to define a function $half : \mathbb{N} \to \mathbb{N}$ only for even integers. Traditionally, the way to deal with this situation is either to check the conditions, and declare an error ("throw an exception") if they fail, or return some (incorrect) value if the condition fails perhaps causing serious errors elsewhere.

With propositions as types, there is a better alternative - the function can require, as an additional argument, a _proof_ that a condition is satisfied. For instance, here is such a function.

```haskell
half : (n : ℕ) → Even n → ℕ
half .0 0even = 0
half (succ (succ n)) (p +2even) = succ (half n p)
```

Our definition also illustrates Agda's _dot_ notation. The first argument in the first case being **.0** means that we can infer from types that its value must be zero.

Note that in the second case we must have a pattern of the form $succ(succ (n))$, from which it can be deduced that $p$ has type $Even n$. If we just tried to match to $n$, then we cannot in general reconcile the terms and types.

We may also wish to assert that the result of functions have some additional property - for instance that a function returns a _sorted_ list. This is best achieved if the value of the function includes a proof that the condition holds. For example, the following function doubles a number and also gives evidence that it is even.

```haskell
double : (n : ℕ) → Σ ℕ Even
double 0 = [ 0 , 0even ]
double (succ n) = [ (succ (succ (proj₁ (double n)))) , (proj₂ (double n)) +2even ]
```

We can use the proof provided by such a function to apply a function that requires a proof.

```haskell
halfdouble : ℕ → ℕ
halfdouble n = half (proj₁ (double n)) (proj₂ (double n))
```

### The Collatz function.

As a more complex example, we construct the  function governing the [Collatz conjecture](http://en.wikipedia.org/wiki/Collatz_conjecture), which maps a natural number  $n$ to $n/2$ if $n$ is even, and $3n + 1$ if $n$ is odd, or equivalently $n+1$ is even. We use our halving function  with proof, and the proof that one of $n$ and $n+1$ is even.

```haskell
module Collatz where
  frompf : (n : ℕ) → n|n+1even.P n → ℕ
  frompf n (ι₁ p) = half n p
  frompf n (ι₂ p) = (3 * n) + 1

  fn = λ n → frompf n (n|n+1even.thm n)
```

Note that we access a term _T_ in the module _n\|n+1even_ from outside the module by prefacing it with _n\|n+1even._ to get _n\|n+1even.T_.


###The identity type###

One of the most fundamental concepts in homotopy type theory is the identity type family, representing equality between objects with a given type. This is an inductive type family, generated by the reflexivity constructor giving an equality between an object and itself.

```haskell The identity type
data _==_ {A : Type} : A → A → Type where
  refl : (a : A) → a == a
```

Note that while this is an inductive type family, for a fixed object a the type $a==a$ is *not* an inductive type defined by $refl(a)$, i.e., we cannot define (dependent) functions on this type but just defining them on the reflexivity constructor. This is a subtle point, which will become clearer as we look at the topological interpretation. We shall study the identity type extensively.

For now, let us show some basic properties of the identity type. All these are proved by constructing proof terms by induction. These are in a separate module **Id**.


Firstly, we see that equality (given by the identity type) is symmetric and transitive. Symmetry is straightforward.

```haskell
sym : {A : Type} → {x y : A} → x == y → y == x
sym (refl x) = refl x
```

Next, we see transitivity of equality, for which we use $\\&\\&$ as notation.

```haskell
_&&_ : {A : Type} → {x y z : A} → x == y → y == z  → x == z
_&&_ (refl a) (refl .a) = refl a
```

We have once more used the *dot notation*. Notice that we have a term **.a** - this says that we can deduce, *from the types*, that $a$ is the only possibility at its position in the pattern.

If two terms are equal, then the terms resulting from applying a function to them are also equal. We prove this next.

```haskell
_#_ : {A B : Type} → {x y : A} → (f : A → B) → x == y → (f x) == (f y)
f # (refl x) = refl (f x)
```


As we see, we can express all the usual mathematical statements using types built up using our basic constructions: inductive types, functions and dependent functions. We have also seen that the basic rules for constructing objects are powerful rules of deduction. However, there are some things they cannot deduce, for instance the statement (called the axiom of extensionality) that if $f, g: A\to B$ are function with $f(a)=g(a)$ for all $a \in A$, then $f=g$. Hence, we have to introduce this as a postulate - we just postulate that  there is an object (which we give a name) of a given type.

```haskell
postulate
  extensionality : {A B : Type} → (f g : A → B) → ((x : A) → (f x) == (g x)) → f == g
```

We can similarly introduce axioms specific to a domain, say Euclidean geometry, by postulating them in a module.
