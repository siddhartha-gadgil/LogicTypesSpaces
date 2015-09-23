open import Base

open import Nat
open import Fin

module Tree where

data RootedTree (A : Type) : Type where
  leaf : A → RootedTree A
  node : (n : ℕ) → (Fin(n) → RootedTree A) → RootedTree A
