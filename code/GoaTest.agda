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


