module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ m) + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = n + (m * n)


factorial : ℕ → ℕ
factorial zero = succ zero
factorial (succ n) = (succ n) * (factorial n)

{-
forever : ℕ → ℕ
forever zero = zero
forever (succ n) = forever (succ (succ n))
-}

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}

open import BoolType

_eqls_ : ℕ → ℕ → Bool
zero eqls zero = true
zero eqls (succ n) = false
(succ m) eqls zero = false
(succ n) eqls (succ m) = n eqls m
