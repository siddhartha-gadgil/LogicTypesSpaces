open import Base

module IIScLecture where 

data Bool : Type where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

two = succ (succ zero)

_+_ :  ℕ → ℕ → ℕ
zero + x = x
(succ n) + x = succ ( n + x)

data Vector : ℕ → Type where
  [] : Vector zero
  _::_ : { n : ℕ} → ℕ → Vector n → Vector (succ n)

{-# BUILTIN NATURAL ℕ #-}

countdown : (n : ℕ) → Vector n
countdown 0 = []
countdown (succ n) = (succ n) :: (countdown n)

sum : {n : ℕ} → Vector n → ℕ
sum [] = 0
sum (x :: v) = x + sum v

data isEven : ℕ → Type where
  0even : isEven 0
  +2even :
