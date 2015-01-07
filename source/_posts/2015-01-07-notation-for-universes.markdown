---
layout: post
title: "Notation for Universes"
date: 2015-01-07 09:25:59 +0530
comments: true
categories:
---

Agda uses the notation **Set** for the first universe. This is incorrect from the point of view of Homotopy type theory, as not all types in this universe are sets. Following HoTT-Agda, we shall denote this instead as **Type**. We accordingly modify the definition of Booleans.

```haskell
Type : Set₁
Type = Set

data Bool : Type where
  true   : Bool
  false  : Bool
```

The statement **Bool : Type** should be read as saying that **Bool** has type **Type**, which implies in particular that it is a type. This is analogous to an expression like **3 : Int** in a programming language, which says that **3** is an integer.

Note that **Type** itself has to have type in a higher universe to avoid Russel's paradox. Agda (like HoTT) has a hierarchy of such universes, $Set = Set\_0$, $Set\_1$ etc.
