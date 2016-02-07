open import Base

module GoaLive where

data Bool : Type where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

notnot : Bool → Bool
notnot x = not(not x)

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero + x = x
(succ n) + x = succ (n + x)

two = succ (succ zero)

data Vector : ℕ → Type where
  [] : Vector zero
  _::_ : {n : ℕ} → ℕ → Vector n → Vector (succ n)

{-# BUILTIN NATURAL ℕ #-}

countdown : (n : ℕ) → Vector n
countdown 0 = []
countdown (succ n) = (succ n) :: (countdown n)

sum : {n : ℕ} → Vector n → ℕ
sum [] = 0
sum (x :: v) = x + sum v

data isEven : ℕ → Type where
  0even : isEven 0
  +2even : (n : ℕ) → isEven n → isEven (succ(succ n))

4even : isEven 4
4even = +2even _ (+2even _ 0even)

data False : Type where

1odd : isEven 1 → False
1odd ()

3odd : isEven 3 → False
3odd (+2even .1 ())

{-
2odd : isEven 2 → False
2odd (+2even .0 0even) = {!!}
-}

half : (n : ℕ) → isEven n → ℕ
half .0 0even = 0
half .(succ (succ n)) (+2even n pf) = half n pf

double : ℕ → ℕ
double zero = zero
double (succ n) = succ (succ (double n))

thm : (n : ℕ) → isEven (double n)
thm zero = 0even
thm (succ n) = +2even _ (thm n)
