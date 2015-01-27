open import Base

module Logic where

mp : {A B : Type} → A → (A → B) → B
mp a f = f a

open import Nat

data Even : (n : ℕ) → Type where
  0even : Even 0
  +2even : {n : ℕ} → Even n → Even (succ (succ n))

4even : Even 4
4even = +2even (+2even 0even)

P : ℕ → Type
P = λ n → (Even n) ⊕ (Even (succ n))

step : {n : ℕ} → P(n) → P(succ n)
step (ι₁ p) = ι₂ (+2even (succ p))
step (ι₂ p) = ι₁ p

