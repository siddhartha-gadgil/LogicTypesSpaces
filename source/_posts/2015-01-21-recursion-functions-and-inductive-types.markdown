---
layout: post
title: "Recursion functions and Inductive Types"
date: 2015-01-21 08:36:41 +0530
comments: true
categories:
---

We have constructed various inductive types, and constructed functions on these types recursively. We have however not addressed the issue of what are valid definitions for inductive types and recursive functions. We now turn to these questions. The definition of inductive types we now consider is not the most general, but it includes all the examples so far.

### Examples recalled

Suppose now that we wish to define an inductive type $W$. We recall two previous types we have defined. For $W = \mathbb{N}$, we used the following  definition.

``` haskell
data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ
```

Lists are a parametrized inductive type, which means that for each type $A$ we get a list of type $A$. We focus on the case where $A =\mathbb{N}$, so the inductive definition of $List\mathbb{N}=List\  \mathbb{N}$ becomes the following.

```haskell
data Listℕ : Type where
  [] : Listℕ
  _::_ : ℕ → Listℕ → Listℕ

```  

## Constructors.

The inductive type $W$ is defined by constructors, which are curried functions that give an element in $W$, with the arguments possibly in $W$. In the above examples, the constructors have types:

* For $W = \mathbb{N}$, $zero$ has type $W$ and $succ$ has type $W \to W$.
* For $W = List\mathbb{N}$, $[]$ has  type $W$ and $\\\_::\\\_$ has  type $\mathbb{N}\to W \to W$.

It is clear how to generalize these. A constructor for a type $W$ can be:

* $W$ itself (which we can think of as a function of no arguments giving $W$, i.e. $W = \to W$).
* obtained from a constructor type  $T =\dots \to W$ by mapping $W$ to this constructor type to get $W \to T = W \to \dots \to W$.
* obtained from a constructor type $T = \dots \to W$ by mapping a type $A$ not involving $W$ to this constructor type to get $A \to T = A \to \dots \to W$.

We shall later see some other ways of building constructors. For the present, observe that all our examples so far, $\mathbb{N}$, $List A$, $Bool$, $A \times B$ and $A \oplus B$  are  all of this form. We shall next see what we mean by recursive definitions on such inductive types.

## Recursive definitions.

We shall associate with an inductively defined type $W$ and another type $X$ a function $rec\_{W, X}$ which has arguments the ingredients of a recursive definition and gives a function from $W$ to $X$. So the type of $rec\_{W, X}$ is  of the form $\dots \to (W \to X)$.

First, consider the case when $W = \mathbb{N}$. A recursive function $f: W \to X$ is defined by specifying its value on $zero$ and on $succ(n)$ for $n \in \mathbb{N}$. These values in turn are determined by terms, whose types we call $D\_{zero}$ and $D\_{succ}$. In terms of these, the type of $rec\_{\mathbb{N}, X}$ is thus $D\_{zero} \to D\_{succ} \to \mathbb{N}$.

The function $f$ is determined on $zero$ by simply specifying its image $f(zero) : X$, so $D\_{zero}$ is just $X$. On the other hand, for $n : \mathbb{N}$, $f(succ(n))$ is a function of $n$ and $f(n)$. So specifying the image of $f$ on all numbers of the form $f(succ(n))$ amounts to giving a function $\mathbb{N} \to X \to X$, with the first argument to be applied to $n$ and the second to $f(n)$.

Thus, the recursion function of $\mathbb{N}$ has the type

$$rec_{\mathbb{N}, X} : X \to (\mathbb{N} \to X \to X) \to (\mathbb{N} \to X)$$

Next, consider the case of lists of natural numbers. Again, we define a function $f$ recursively to a type $X$ in terms of the value on the result of each constructor. For the empty list, the value of $f$ is simply given by $f([]) : X$. On the other hand, for a list of the form $head :: tail$, the value of $f$ can be a function of $head$, $tail$ and $f(tail)$. Thus, we have a recursion function with the type

$$rec_{List \mathbb{N}, X} : X \to (\mathbb{N} \to List \mathbb{N} \to X \to X) \to (List \mathbb{N} \to X)$$

It is easy to generalize these examples to an inductive type $W$ of the form we are considering. Namely, we associate to a constructor type $T$ a recursion data type $R\_X(T)$ as follows:

* if $T = W$, $R\_X(T) = X$
* if $T = W \to T'$, $R\_X(T) = W \to X \to R\_X(T')$
* if $T = A \to T'$ with $A$ independent of $W$, then $R\_X(T) = A \to R\_X(T')$

These rules tell us the type of the recursion functions. The recursion function satisfies certain _definitional equalities_, saying that it acts on the image of constructors as specified. For example, in the case of natural numbers, we get the identities:

* $rec\_{\mathbb{N}, X} (z) (f) (0) \equiv z$,
* $rec\_{\mathbb{N}, X} (z) (f) (succ(n)) \equiv f (n) (rec\_{\mathbb{N}, X} (z) (f) (n))$.

In homotopy type theory, we view an inductive definition as introducing a type, constructor functions, a recursion function and certain definitional equalities. We shall see later the final ingredients of an inductive type definition, namely a so called _induction function_ and corresponding definitional equalities.

In terms of Agda code, we can simply define the recursion functions. For instance, for natural numbers, we have:

```haskell
recℕ : {X : Type} → X → (ℕ → X → X) → (ℕ → X)
recℕ z f zero = z
recℕ z f (succ n) = f n (recℕ z f n)
```

We shall construct the recursion functions in the other cases later. First, we shall see that we can make recursive definitions using the recursion function, without any pattern matching. In terms of Agda code, this means we need to use pattern matching only once - to construct the recursion function. In terms of homotopy type theory, all we use is that we have a recursion function of the appropriate type and that the corresponding definitional equalities hold.

## Definitions using the recursion function.

We turn to examples of definitions using recursion functions. First we define the factorial. Note that in this definition $n!$ is just a variable name.

```haskell
_! : ℕ → ℕ
_! = recℕ 1 (λ n n! → (n + 1) * n!)
```

Next, we define addition using the recursion function. This is a curried function $\\\_plus\\\_ : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$, so $\\\_plus\\\_ (0) = 0\\ plus\\ \\\_$ is a function, namely the identity. Similarly $\\\_plus\\\_ (succ(n)) = (succ (n))\\ plus\\ \\\_$ is a function defined in terms of $n$ and $n\\ plus\\ \\\_$, where $n\\ plus\\ \\\_$ is the function _addition by $n$_ (we use the variable name $nplus = \\\_ plus\\\_ (n)$). Clearly the following is a definition of addition (we have written this using nested lambdas for clarity).

```haskell
_plus_ : ℕ → ℕ → ℕ
_plus_ = recℕ (λ n → n) (λ n nplus → (λ m → succ (nplus m)))

```

Multiplication can be  defined similarly

```haskell
_times_ : ℕ → ℕ → ℕ
_times_ = recℕ (λ n → 0)(λ n ntimes → (λ m → (ntimes m) plus m))
```

## Foundations so far.

As you can observe, we have now defined functions purely in terms of lambdas and recursion function. Thus, we now have clear foundation rules. Namely,

* We have (so far) two ways of constructing types - inductive types and function types.
* Terms can be constructed by applying a function $f: A \to B$ to a term $a : A$. We make the judgment $f(a) : B$.  
* Terms of function types are constructed using lambdas. A $\lambda$-term $A \to B$ is of the form $\lambda a \mapsto b$ where $b$ is an expression of type $b$, which can involve the variable (term)
$a : A$ and is otherwise built using the usual rules for forming terms.
* An inductive type $W$ is specified by specifying the types of constructors. The type of a constructor is built from $W$ in certain specified ways.
* When defining an inductive type, we define constructors as terms of the specified type.
* For an inductive type $W$ and a type $X$, we obtain a recursion function $rec\_{W, X}$, whose type is determined in terms of the constructors of $W$. We have certain _computation_ rules giving definitional equalities for the action of a recursively defined function on the image of a constructor.

We need a few more rules of a similar nature, mainly concerned with extending rules involving functions to so called _dependent functions_. Our next goal is to introduce dependent functions.

## Exercise

* Define the recursion functions $recBool$ on Booleans.
* Define the recursion function $recList(A)$ as a function of $A : Type$.
* Define $not$, $\\\_ \\& \\\_$  and $\\\_contains\\\\_$ in terms of the above recursion functions without using any pattern matching.
