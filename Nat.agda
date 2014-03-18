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


 