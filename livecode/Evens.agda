{-# OPTIONS --without-K #-}

open import Base

open import Nat

open import Logic

module Evens  where

data Even : ℕ → Type where 
  0even : Even 0
  _+2even : {n : ℕ} → Even n → Even (succ (succ n))

4even = (0even +2even) +2even 

1odd : Even 1 → False
1odd ()

module n|n+1even where
  P : ℕ → Type
  P n = (Even n) ⊕ (Even (succ n))

  step : {n : ℕ} → P n → P (succ n)
  step (ι₁ p) = ι₂(p +2even)
  step (ι₂ p) = ι₁ p

  thm : (n : ℕ) → P n
  thm 0 = ι₁ 0even
  thm (succ n) = step (thm n) 

value : {n : ℕ} → Even n → ℕ
value 0even = 0
value (p +2even) = succ (succ (value p))

half : (n : ℕ) → Even n → ℕ
half .0 0even = 0
half (succ (succ n)) (p +2even) = succ (half n p)

double : (n : ℕ) → Σ ℕ Even
double 0 = [ 0 , 0even ]
double (succ n) = [ (succ (succ (proj₁ (double n)))) , (proj₂ (double n)) +2even ]

halfdouble : ℕ → ℕ
halfdouble n = half (proj₁ (double n)) (proj₂ (double n))



module Collatz where
  open n|n+1even

  frompf : (n : ℕ) → P n → ℕ
  frompf n (ι₁ p) = half n p
  frompf n (ι₂ p) = (3 * n) + 1

  fn = λ n → frompf n (thm n) 
