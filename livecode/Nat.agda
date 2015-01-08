module Nat where

Type : Set₁
Type = Set

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

two : ℕ
two = succ (succ zero)

_+_ : ℕ → ℕ → ℕ
zero + y = y
(succ n) + y = succ (n + y)

forever : ℕ → ℕ
forever zero = zero
forever (succ x) = forever (succ (succ x))
 
