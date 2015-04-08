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

rec : {A : Type} → (X : Type) → (A → X) → ({n : ℕ} → (Fin n → Tree A) → (Fin n → X) → X) → Tree A → X
rec X f<leaf?> d (leaf a) = f<leaf?> a
rec X f<leaf?> d (node φ) = d φ (λ a → (rec X f<leaf?> d) (φ a)) 
-- f = rec X f<leaf?> d
  
