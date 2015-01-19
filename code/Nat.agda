open import Base

module Nat where


data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ -- the successor of a number

two : ℕ
two = succ (succ zero)

_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ n) + y = succ (n + y)

{-
forever : ℕ → ℕ
forever zero = zero
forever (succ x) = forever (succ (succ x))
-} 

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC succ #-}

_*_ : ℕ → ℕ → ℕ
zero * _ = zero
(succ n) * m = (n * m) + m


factorial : ℕ → ℕ
factorial zero = 1
factorial (succ n) = (succ n) * (factorial n)
