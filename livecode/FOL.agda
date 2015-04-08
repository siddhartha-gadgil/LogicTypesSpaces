open import Base

open import Nat

module FOL(Var Const : Set)(Func : ℕ → Set)(Pred : ℕ → Set) where

open import Fin

data Term : Type where
  const : Const → Term
  var : Var → Term
  _apply_ : {n : ℕ} → Func n → (Fin n → Term) → Term

data AtomicFormula : Type where
  _apply_ : {n : ℕ} → Pred n → (Fin n → Term) → AtomicFormula

data RecursiveFormula (Base : Set) : Type where
  atom : Base → RecursiveFormula(Base)
  ¬ : RecursiveFormula Base → RecursiveFormula Base
  _=>_ : RecursiveFormula Base → RecursiveFormula Base → RecursiveFormula Base
  _<=>_ : RecursiveFormula Base → RecursiveFormula Base → RecursiveFormula Base
  _∧_ : RecursiveFormula Base → RecursiveFormula Base → RecursiveFormula Base
  _∨_ : RecursiveFormula Base → RecursiveFormula Base → RecursiveFormula Base
  ForAll : Var → RecursiveFormula Base → RecursiveFormula Base
  Exists : Var → RecursiveFormula Base → RecursiveFormula Base

Formula = RecursiveFormula AtomicFormula

open import Boolean
  
data Interpretation (M : Set) : Type where
  φ : (Const → M) → ({n : ℕ} → Func n → (Fin n → M) → M) → ((n : ℕ) → Pred n → (Fin n → M) → Bool) → Interpretation M 

term : {M : Set} → Interpretation M → (Var → M) → Term → M
term (φ x x₁ x₂) ξ (const x₃) = x x₃
term α ξ (var x) = ξ x
term (φ x x₁ x₂) ξ (x₃ apply x₄) = x₁ x₃ (λ a → term (φ x x₁ x₂) ξ (x₄ a))

recBool : {Base : Set} → (Base → Bool) → RecursiveFormula Base → Bool
recBool α (atom x) = α x
recBool α (¬ fmla) = not (recBool α fmla)
recBool α (fmla => fmla₁) = {!!}
recBool α (fmla <=> fmla₁) = {!!}
recBool α (fmla ∧ fmla₁) = recBool α fmla & recBool α fmla₁
recBool α (fmla ∨ fmla₁) = {!!}
recBool α (ForAll x fmla) = {!!}
recBool α (Exists x fmla) = {!!}

Axioms = Formula → Bool

isTrue : {M : Set} → Interpretation M → Formula → Bool
isTrue (φ x x₁ x₂) (atom (x₃ apply x₄)) = {!!}
isTrue (φ x x₁ x₂) (¬ fmla) = {!!}
isTrue (φ x x₁ x₂) (fmla => fmla₁) = {!!}
isTrue (φ x x₁ x₂) (fmla <=> fmla₁) = {!!}
isTrue (φ x x₁ x₂) (fmla ∧ fmla₁) = {!!}
isTrue (φ x x₁ x₂) (fmla ∨ fmla₁) = {!!}
isTrue (φ x x₁ x₂) (ForAll x₃ fmla) = {!!}
isTrue (φ x x₁ x₂) (Exists x₃ fmla) = {!!}

data Theory (axioms : Axioms) : Set₁ where
  theory : {M : Set} → (interp : Interpretation M) → (fmla : Formula) → (axioms fmla) == true → (isTrue interp fmla) == true → Theory axioms 
