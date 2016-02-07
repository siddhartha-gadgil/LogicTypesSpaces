open import Base

module CMItest where

data Bool : Type where
  true : Bool
  false : Bool

idBool : Bool → Bool
idBool x = x

alwaysTrue : Bool → Bool
alwaysTrue _ = true

not : Bool → Bool
not true = false
not false = true

notnot : Bool → Bool
notnot x = not(not x)

_&_ : Bool → Bool → Bool
true & x = x
false & _ = false

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

even : ℕ → Bool
even zero = true
even (succ x) = not (even x)

_+_ : ℕ → ℕ → ℕ
zero + x = x
(succ n) + x = succ(n + x)

{-# BUILTIN NATURAL ℕ #-}

data Vector : ℕ → Type where
  [] : Vector 0
  _::_ : {n : ℕ} → ℕ → Vector n → Vector (succ n)

onetwothree = 1 :: (2 :: (3 :: []))

sum : {n : ℕ} → Vector n → ℕ
sum [] = 0
sum (a :: xs) = a + (sum xs)

countdown : (n : ℕ) → Vector n
countdown 0 = []
countdown (succ n) = (succ n) :: (countdown n)

sumToN : ℕ → ℕ
sumToN x = sum (countdown x)

data isEven : ℕ → Type where
  0even : isEven 0
  +2even : (n : ℕ) → isEven n → isEven (succ (succ n))

4even : isEven 4
4even = +2even _ (+2even _ 0even)

data False : Type where

1odd : isEven 1 → False
1odd ()

3odd : isEven 3 → False
3odd (+2even .1 ())

half : (n : ℕ) → isEven n → ℕ
half .0 0even = 0
half .(succ (succ n)) (+2even n pf) = succ (half n pf)

double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ (double n))

thm : (n : ℕ) → isEven (double n)
thm zero = 0even
thm (succ m) = +2even _ (thm m)

halfOfDouble : ℕ → ℕ
halfOfDouble n = half (double n) (thm n)
