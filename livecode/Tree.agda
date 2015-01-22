open import Base

module Tree where

data BinTree (A : Type) : Type where
  leaf : A → BinTree A
  node : BinTree A → BinTree A → BinTree A

