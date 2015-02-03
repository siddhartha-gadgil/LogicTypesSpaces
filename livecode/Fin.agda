{-# OPTIONS --without-K #-}


open import Base

module Fin where

open import Nat


data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

_asℕ : {n : ℕ} → Fin n → ℕ
fzero asℕ = 0
(fsucc k) asℕ = succ (k asℕ)
 
finhead : {A : Type} → {n : ℕ} → (Fin (succ n) → A) → A
finhead f = f (fzero)

fintail : {A : Type} → {n : ℕ} → (Fin (succ n) → A) → (Fin n) → A
fintail f = λ k → f (fsucc k)

_:::_ : {A : Type} → {n :  ℕ} → A → (Fin n → A) → (Fin (succ n) → A)
(a ::: f) (fzero) = a
(a ::: f) (fsucc n) = f n 

open import Vector

finFn : {A : Type} → {n : ℕ} → Vec A n → Fin n → A
finFn [] ()
finFn (head :: tail) fzero = head
finFn (head :: tail) (fsucc k) = finFn tail k

vect : {A : Type} → (n : ℕ) → (Fin n → A) → Vec A n
vect 0 _ = []
vect (succ n) f = (finhead f) :: (vect n (fintail f))