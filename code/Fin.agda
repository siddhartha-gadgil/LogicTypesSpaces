open import Base
open import Nat

module Fin where

data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (succ n)
  fsucc : {n : ℕ} → Fin n → Fin (succ n)

