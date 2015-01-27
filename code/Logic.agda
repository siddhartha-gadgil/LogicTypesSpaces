open import Base

module Logic where

mp : {A B : Type} → A → (A → B) → B
mp a f = f a

open import Nat

data False : Type where

data True : Type where
  qed : True

data Even : (n : ℕ) → Type where
  0even : Even 0
  +2even : {n : ℕ} → Even n → Even (succ (succ n))

4even : Even 4
4even = +2even (+2even 0even)

P : ℕ → Type
P = λ n → (Even n) ⊕ (Even (succ n))

step : {n : ℕ} → P(n) → P(succ n)
step (ι₁ p) = ι₂ (+2even p)
step (ι₂ p) = ι₁ p

n|n+1even : (n : ℕ) → P(n)
n|n+1even 0 = ι₁ 0even
n|n+1even (succ n) = step (n|n+1even n)

1odd : (Even 1) → False
1odd ()

value : {n : ℕ} → Even n → ℕ
value 0even = 0
value (+2even p) = succ (value p) 

half : {n : ℕ} → Even n → ℕ
half  0even = 0
half  (+2even p) = succ (value p) 

double : (n : ℕ) → Σ ℕ Even
double 0 = [ 0 , 0even ]
double (succ n) = [ succ (succ (proj₁ (double n))) , +2even (proj₂ (double n)) ]

halfdouble : ℕ → ℕ
halfdouble n = half (proj₂ (double n))
