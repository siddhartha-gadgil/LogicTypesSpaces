open import Base

open import Nat

module Evens where

data Even : ℕ → Type where
  0even : Even 0
  _+2even : {n : ℕ} → Even n → Even (succ (succ n))

4even : Even 4
4even = (0even +2even) +2even

open import Logic

1odd : Even 1 → False
1odd ()

module n|n+1even where
  P = λ n → (Even n) ⊕ (Even (succ n))

  step : {n : ℕ} → P n → P (succ n)
  step (ι₁ p) = ι₂(p +2even)
  step (ι₂ p) = ι₁(p)

  thm : (n : ℕ) → P n
  thm 0 = ι₁ 0even
  thm (succ n) = step (thm n)

value : {n : ℕ} → Even n → ℕ
value 0even = 0
value (p +2even) = succ (succ (value p))

half : (n : ℕ) → Even n → ℕ
half .0 0even = 0
half (succ (succ n)) (p +2even) = succ (half n p) 

-- wrong = half 2 0even

double : ℕ → Σ ℕ Even
double 0 = [ 0 , 0even ]
double (succ n) = [ succ (succ (proj₁(double n))) , (proj₂ (double n) +2even) ]

halfdouble : ℕ → ℕ
halfdouble n = half (proj₁ (double n)) (proj₂ (double n))

