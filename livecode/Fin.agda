open import Base

module Fin where

open import Nat

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

_asℕ : {n : ℕ} → Fin n → ℕ
fzero asℕ = 0
(fsucc k) asℕ = succ (k asℕ)
 
