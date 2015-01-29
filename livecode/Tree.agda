open import Base

module Tree where

open import Nat

open import Fin

data BinTree (A : Type) : Type where
  leaf : A → BinTree A
  node : BinTree A → BinTree A → BinTree A

data Tree (A : Type) : Type where
  leaf : A → Tree A
  node : {n : ℕ} → (Fin n → Tree A) → Tree A
