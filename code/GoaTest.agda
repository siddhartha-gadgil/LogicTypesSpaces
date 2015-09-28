open import Base

module GoaTest where

data Bool : Type where -- finite type
  true : Bool
  false : Bool

idBool : Bool → Bool -- lambda
idBool x = x

alwaysTrue : Bool → Bool
alwaysTrue x = true

not : Bool → Bool -- case defn
not true = false
not false = true

notnot : Bool → Bool -- lambda
notnot x = not(not(x))

_&_ : Bool → Bool → Bool --curried function
true & x = x
false & _ = false

data ℕ : Type where -- infinite type
  zero : ℕ
  succ : ℕ → ℕ

even : ℕ → Bool -- recursive definition
even zero = true
even (succ x) = not (even x)

_+_ : ℕ → ℕ → ℕ 
zero + y = y
succ x + y = x + succ y

{-# BUILTIN NATURAL ℕ #-}

data ℕList : Type where --list type
  [] : ℕList
  _::_ : ℕ → ℕList → ℕList


data Vector : ℕ → Type where -- type family
  [] : Vector 0
  _::_ : {n : ℕ} → ℕ → Vector n → Vector (succ n) 

sum : {n : ℕ} → Vector n → ℕ
sum [] = 0
sum (x :: l) = x + sum l


countdown : (n : ℕ) → Vector n -- dependent function
countdown 0 = []
countdown (succ n) = (succ n) :: (countdown n)

sumToN : ℕ → ℕ -- calculation
sumToN n = sum(countdown n)

data isEven : ℕ → Type where
  0even : isEven 0
  +2even : (n : ℕ) → isEven n → isEven (succ(succ(n)))

4even : isEven 4
4even = +2even _ (+2even _ 0even)

data False : Type where

1odd : isEven 1 → False
1odd ()

3odd : isEven 3 → False
3odd (+2even .1 ())

half : (n : ℕ) → isEven n → ℕ
half .0 0even = 0
half .(succ (succ n)) (+2even n pf) = half n pf

double : (n : ℕ) → ℕ
double 0 = 0
double (succ n) = succ(succ(double(n)))

step : (n : ℕ) → (isEven (double n)) → isEven (double(succ(n)))
step n pf = +2even _ pf

thm : (n  : ℕ) → isEven (double n)
thm zero = 0even
thm (succ n) = step _ (thm n)
