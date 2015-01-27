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
recℕ z f zero = z
recℕ z f (succ n) = f n (recℕ z f n)

_! : ℕ → ℕ 
_! = recℕ 1 (λ n n! → (n + 1) * n!) 

_plus_ : ℕ → ℕ → ℕ
_plus_ = recℕ (λ n → n) (λ n nplus → (λ m → succ (nplus m)))

_times_ : ℕ → ℕ → ℕ
_times_ = recℕ (λ n → 0)(λ n ntimes → (λ m → (ntimes m) plus m)) 
