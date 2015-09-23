open import Base

open import Nat

open import Fin

module FOL (Var Const : Set)(Func : ℕ → Set)(Pred : ℕ → Set) where

data Term : Type where
  var : Var → Term
  const : Const → Term
  recTerm : {n : ℕ} → Func(n) → (Fin(n) → Term) → Term

data Formula : Type where
  atomic : {n : ℕ} → Pred n → (Fin(n) → Term) → Formula
  _=>_ : Formula → Formula → Formula
  _<=>_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  ¬ : Formula → Formula
  ForAll : Var → Formula → Formula
  Exists : Var → Formula → Formula

module IntWrap (n : ℕ) where
  double = n + n

d : ℕ → ℕ
d n = I.double where 
  module I = IntWrap n
