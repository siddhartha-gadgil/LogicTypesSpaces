---
layout: post
title: "Constructing Dependent functions"
date: 2015-01-23 10:21:48 +0530
comments: true
categories:
---

While we have introduced dependent functions, we do not formally have any way to construct them - those constructed so far used pattern matching. We shall generalize the two ways we have seen to construct functions, _lambdas_ and using _recursion functions_ to constructions of dependent functions. In doing so we also review and clarify the case of ordinary functions.

## Lambdas

We can construct a function of type $A \to B$ as a lambda, i.e., we consider an $\\lambda$-expression $\\lambda a \\to b$, which is usually denoted $a \mapsto b$ in mathematics. More precisely,

* $a$ is a variable of type $A$. This is just a term with a name, which we temporarily introduce. Note that the type $A$ may not have any terms at all.
* $b$ is an expression (judgmentally) of type $B$ which can involve $a$. This means that $b$ is a term formed by the usual rules for forming terms - applying a function to an argument, constructing function types, lambdas etc., except that we can use the term $a : A$ along with other terms previously introduced to the context.
* When we apply $\lambda a \to b$ to $a' : A$, we obtain the result of _substituting_ $a'$ for $a$ in $b$. For this to be meaningful, it is to be understood that our rules for forming terms include rules for _substitution_.

It is clear how to generalize this to obtain dependent functions, with type say $\\Pi\_{a : A} B(a)$. Namely, we consider terms $\\lambda a \\to b$ so that the expression $b$ has type $B(a)$.

## Recursion functions revisited.

Functions on inductive types can be constructed using associated recursion functions. We clarify this in the case of the simple inductive types we have considered so far, and extend this to some more general inductive types.

#### Constructors for $W$

For a type $W$, previously, we considered constructors as terms with type that can be obtained in the following ways.

* $W$ itself can be the type of a constructor.
* If $T$ is the type of a constructor, then $W \\to T$ can also be a type of a constructor for $W$.
* If $T$ is the type of a constructor and $A$ is a type not involving $W$, then $A \\to T$ can also be a type of a constructor for $W$.

It may seem that any type $X$ should fall into one of the latter two cases, but this is not so. For example $W \to W$ is not in either case, and indeed $(W \to W) \to W$ is not a valid type for a constructor.

Observe that for a constructor $g$ of the type $W \to T$, if $w : W$ then $g(w)$ is also a constructor, and we have a similar statement for the type being $A \to T$.

We now look at two more ways of obtaining constructors, with functions in the second and third rule above generalized to dependent functions.

* If we have a function associating to $w : W$ the type $T(w)$ of a constructor for $W$, then $\Pi_{w : W} T(w)$ can also be the type of a constructor.
* If $A$ is a type not involving $W$ and we have a function associating to $a : A$ the type $T(a)$ of a constructor for $W$, then $\Pi_{a : A} T(a)$ can also be the type of a constructor.


#### Domains of Recursion

Given a constructor $\varphi$ for $W$ and a type $X$, we obtain a type which we call the _domain of recursion_ of $\varphi$ and denote $R\_{W, X}(\varphi)$. For constructors obtained using the above rules, we define this as follows. Note that we could have defined this purely in terms of the type of $\varphi$, but we chose the definition to be parallel to the case for dependent functions.

* If $\varphi : W$, then $R\_{W, X}(\varphi) = X$.
* If $\varphi : W \to T$ and $w : W$ is a variable (or term), then $R\_{W, X}(\varphi) = W \to X \to R\_{W, X}(\varphi(w))$. Note that this does not depend on the choice of $w : W$. Indeed it is determined by the type $T$ of $\varphi(w)$.
* If $\varphi : A \to T$ and $a : W$ is a variable (or term), then $R\_{W, X}(\varphi) = A \to R\_{W, X}(\varphi(w))$. Note that this does not depend on the choice of $a : A$. Indeed it is determined by the type $T$ of $\varphi(a)$.
* If $\varphi : \Pi\_{w: W} T(w)$, then $R\_{W, X}(\varphi) = \Pi\_{w: W} (W \to X \to R\_{W, X}(\varphi(w))).$
*  If $\varphi : \Pi\_{a: A} T(a)$ with the type $A$ not involving $W$, then $R\_{W, X}(\varphi) = \Pi_{a: A} (A \to R\_{W, X}(\varphi(w))).$

If we have a type such as $W \to W$ that involves $W$ but is not equal to $W$, it is not clear whether the second or third ruls applies. We shall eventually allow some such types, but not others. For these we will extend the rules for $W$.

#### The recursion function

Suppose now that $W$ is given by constructors $\varphi_1$, $\dots$, $\varphi_k$. Then when defining $W$, we introduce for each type $X$ a term $rec\_{W, X}$ with type

$$rec_{W, X} : R_{W, X}(\varphi_1) \to \dots \to R_{W, X}(\varphi_k) \to (W \to X)$$

We make certain judgments, giving definitional equalities involving the recursion function.

## Induction functions

It is straightforward to modify the above for definitions of dependent functions. The analogues of recursive definitions for dependent functions are called _inductive definitions_, and these are interpreted in terms of _induction functions_.

#### For natural numbers

First we briefly consider an example, namely dependent functions on $\mathbb{N}$. Suppose $X : \mathbb{N} \to \mathcal{U}$ is a type family. To define inductively a dependent function $f : \Pi\_{n : \mathbb{N}} X(n)$, we must specify

* $f(0)$, of type $X(0)$.
* For all $n$, $f(n + 1) : X(n+1)$ in terms of $n : \mathbb{N}$ and $f(n) : X(n)$.

Thus we require a term of type $X(0)$, and for each $n$, a term of type $X(n+1)$ as a function of a term of type $\mathbb{N}$ and a term of type $X(n)$. The latter data can be viewed as a single term of type $\Pi\_{n : \mathbb{N}} (X(n) \to X(n+1))$. Thus, the induction function for natural numbers has the type

$$ind_{W, X} :  X(0) \to \Pi_{n : \mathbb{N}} (X(n) \to X(n+1)) \to \Pi_{n : \mathbb{N}} X(n).$$

Notice that this type involves the expression $n+1 = succ(n)$, so the type depends on the constructor $\varphi$, not just its type.

#### Domains of induction

Given now a type family $X$, we define for constructors $\varphi$ constructed as above a type $I\_{W, X}(\varphi)$ as follows.

* If $\varphi : W$, then $I\_{W, X}(\varphi) = \Pi_{w: W} X(w)$.
* If $\varphi: W \to T$, then $I\_{W, X}(\varphi) = \Pi\_{w: W} (X(w) \to I\_{W, X}(\varphi(w)))$.
* If $\varphi: A \to T$, then $I\_{W, X}(\varphi) = \Pi\_{a: A} I\_{W, X}(\varphi(a))$.
* If $\varphi: \Pi\_{w: W} T(w)$, then $I\_{W, X}(\varphi) = \Pi\_{w: W} (X(w) \to I\_{W, X}(\varphi(w)))$.
* If $\varphi: \Pi\_{a : A} T(a)$, then $I\_{W, X}(\varphi) = \Pi\_{a: A} I\_{W, X}(\varphi(a))$.

Observe that the constructors involving dependent functions are essentially the same as those involving ordinary functions.

#### The induction function

This can now be introduced in a manner similar to the recursion function. Suppose now that $W$ is given by constructors $\varphi_1$, $\dots$, $\varphi_k$. Then when defining $W$, we introduce for each type family $X$ a term $ind\_{W, X}$ with type

$$rec_{W, X} : I_{W, X}(\varphi_1) \to \dots \to I_{W, X}(\varphi_k) \to (\Pi_{w: W} X(w)).$$

We make certain judgments, giving definitional equalities involving the induction function.


## Inductive type families

We now sketch the generalization to _inductive type families_.

#### Type families

A type family is one of:
* A type $W : \mathcal{U}$.
* A function from a type $A$ to type families.

Thus, a typical type family is $A \to B \to \mathcal{U}$ or $\Pi\_{a : A} (B(a)\to mathcal{U})$.

#### Inductive type families

An inductive type family, say $W : A \to \mathcal{U}$, is a type family which is determined by constructors and for which there are recursion and induction functions. The most important point to note about such a family is that even though, for $a: A$, $W(a)$ is a type, it is **not** an inductive type. For instance, for a type $X$ we do not have a recursion function $rec\_{W(a), X}$. Instead we can recursively (and inductively) define (dependent) functions for all values of the index, i.e., we have a recursion function with type of the form

$$rec_{W, X} : \dots \to \Pi_{a : A}(W(a) \to X)$$

and similarly for inductive functions.

#### Constructors for families.

Consider an inductive type family $W : A \to \mathcal{U}$. It is meaningless to talk of a constructor of type $W$, as $W$ is not a type. Instead basic constructors for such families are of the form $W(a)$ for $a : A$. Similarly, we can extend a constructor $T$ to $W(a') \to T$.

Definitions of recursion and induction functions for type families from constructors are easy generalizations of the definitions for inductive types.
