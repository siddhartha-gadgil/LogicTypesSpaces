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

recℕ : {X : Type} → X → (ℕ → X → X) → (ℕ → X)
recℕ x₀ φ zero = x₀
recℕ x₀ φ (succ n) = φ n (recℕ x₀ φ n)

_! : ℕ → ℕ
_! = recℕ 1 (λ n n! → (succ n) * n!) 

_plus_ : ℕ → (ℕ → ℕ)
_plus_ = recℕ (λ n → n) (λ n nplus → (λ m → succ (nplus m)))

_times_ : ℕ → (ℕ → ℕ)
_times_ = recℕ (λ n → 0) (λ n ntimes → (λ m → m plus (ntimes m)))

suc= : {n m : ℕ} → n == m → (succ n) == (succ m)
suc= (refl n) = refl (succ n)


0rid : (n : ℕ) → (n + 0) == n
0rid 0 = refl 0
0rid (succ n) = suc= (0rid n)

data _≤_ : ℕ → ℕ → Type where
  0≤n : (n : ℕ) → 0 ≤ n
  succ≤ : (a b : ℕ) → (a ≤ b) → ((succ a) ≤ (succ b))

