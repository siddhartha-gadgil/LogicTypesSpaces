---
layout: post
title: "Fin type family"
date: 2015-01-30 10:55:34 +0530
comments: true
categories:
---

We briefly saw the **Fin** type family when constructing trees. We clarify and elaborate on its construction.

The **Fin** type family is indexed by natural numbers $\mathbb{N}$. For $n : \mathbb{N}$, $Fin(n)$ is a finite type with $n$ elements, corresponding to the integers $k$ with $0 \leq k < n$. We denote by $\[k\]\_n$ the element corresponding to the natural number $k$ in $Fin(n)$. Note that $\[1\]\_2$ and $\[1\]\_3$ are **not** the same term even though they correspond to the same natural number.

We define $Fin$ as an inductive type family with two constructors. In Agda, this is as follows.

```haskell
data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)
```

The constructors are similar to the $zero$ and $succ$ constructors for natural numbers. However, as remarked earlier,  $\[0\]\_2$ and $\[0\]\_3$ are **not** the same term, so the constructor $fzero$ takes an argument specifying the type of the term constructed. Since $Fin(0)$ does not have a term corresponding to $0$, but $Fin(k)$ does for $k \geq 1$, we set $fzero(n) = \[0\]\_{n +1}$. Formally, as usual, we only specify the type of $fzero$ and declare it to be a constructor.

The second constructor $fsucc$ takes $\[k\]\_n$ to $\[ k + 1\]\_\{n +1\}$. On the associated natural numbers, this is just the successor function. However it maps the type $Fin(n)$ to the type $Fin(n+1)$ - as one should expect since, given $0 \leq k < n$, we need not have $k + 1 <n$, but always have $0 \leq k+1 \leq n +1$.

Note that if $0\leq k <n$, then there is unique way to obtain $\[k\]\_n$ using the given constructors, namely (using powers to denote iterated application) $\[k\]\_n = fsucc^k (fzero (n -k -1))$.

By a recursive definition, we can define the function $\[k\]\_n \mapsto k$.

```haskell
_asℕ : {n : ℕ} → Fin n → ℕ
fzero asℕ = 0
(fsucc k) asℕ = succ (k asℕ)
```
