module Nat where

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + n = n
(succ m) + n = succ (m + n)

_*_ : ℕ → ℕ → ℕ
zero * n = zero
(succ m) * n = m + (m * n)


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
