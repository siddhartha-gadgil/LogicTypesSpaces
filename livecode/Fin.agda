open import Base

module Fin where

open import Nat

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

_asℕ : {n : ℕ} → Fin n → ℕ
fzero asℕ = 0
(fsucc k) asℕ = succ (k asℕ)
 
finFnhead : {A : Type} → {n : ℕ} → (Fin (succ n) → A) → A
finFnhead f = f(fzero) 

finFntail : {A : Type} → {n : ℕ} → (Fin (succ n) → A) → ((Fin n) → A)
finFntail f k = f (fsucc k)

open import Vector

vec→finFn : {A : Type} → {n : ℕ} → Vec A n → (Fin n → A)
vec→finFn [] ()
vec→finFn (head :: tail) fzero = head
vec→finFn (head :: tail) (fsucc k) = vec→finFn tail k

finFn→vec : {A : Type} → {n : ℕ} → (Fin n → A) → Vec A n
finFn→vec {A} {zero} φ = []
finFn→vec {A} {succ n} φ = (φ fzero) :: finFn→vec (λ k → φ (fsucc k))
