module SumOfSquares where

open import List

open import Nat

upto : ℕ → List ℕ
upto zero = []
upto (succ n) = (upto n) ++ (n :: [])

sqlist : ℕ → List ℕ
sqlist n = (upto n) map (λ x → ((x + 1) * (x + 1)))

sumOfSquares : ℕ → ℕ
sumOfSquares n = fold (sqlist n) by _+_ from 0