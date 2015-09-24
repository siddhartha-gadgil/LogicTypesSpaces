open import Base

module GoaTest where

data Bool : Type where
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

notnot : Bool → Bool
notnot x = not (not x)

and : Bool → Bool → Bool
and true y = y
and false y = false

data ℕ : Type where
  zero : ℕ
  succ : ℕ → ℕ

even : ℕ → Bool
even zero = true
even (succ x) = not (even x)

add : ℕ → ℕ → ℕ
add zero y = y
add (succ x) y = succ (add x y)

{-# BUILTIN NATURAL ℕ #-}

data True : Type where
  qed : True


data False : Type where

data Even : ℕ → Type where
  0even : Even 0
  +2even : (n : ℕ) → Even n → Even (succ (succ n))

2even : Even 2
2even = +2even _ (0even)

half : (n : ℕ) → Even n → ℕ
half .0 0even = {!!}
half .(succ (succ n)) (+2even n pf) = succ (half n pf)

double : ℕ → ℕ
double 0 = 0
double (succ n) = succ (succ(double n))

doubleIsEvenStep : (n : ℕ) → Even (double n) → Even (double (succ n))
doubleIsEvenStep n pf = +2even (double n) pf

doubleIsEven : (n : ℕ) → Even (double n)
doubleIsEven 0 = 0even
doubleIsEven (succ n) = doubleIsEvenStep n (doubleIsEven n)

inducℕ : (P : ℕ → Type) → P(0) → ((n : ℕ) → (P(n) → P(succ n))) → (m : ℕ) → P(m)
inducℕ P 0case step zero = 0case
inducℕ P 0case step (succ m) = step m (inducℕ P 0case step m)
 
