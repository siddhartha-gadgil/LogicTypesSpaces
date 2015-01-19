module LatticePoints where

open import Base

open import Nat

open import List

open import Boolean

open import SumOfSquares

{-
Lists pairs of natural numbers which are in a circle of radius n
-}

_leq_ : ℕ → ℕ → Bool
zero leq _ = true
(succ n) leq zero = false
(succ n) leq (succ m) = n leq m

points : ℕ → List (ℕ × ℕ)
points n = (upto (succ n)) flatMap (λ a → ((upto (succ n)) filter (λ b → ((a * a) + (b * b)) leq (n * n)points )) map (λ b → [ a , b ])) 