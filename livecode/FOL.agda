open import Base

open import Nat

module FOL (Var Const : Set)(Func : ℕ → Set)(Pred : ℕ → Set) where

open import Fin

data Term : Type where
  var : Var → Term
  const : Const → Term
  _apply_ : {n : ℕ} → Func n → (Fin n → Term) → Term


data Formula : Type where
  _apply_ : {n : ℕ} → Pred n → (Fin n → Term) → Formula
  ¬ : Formula → Formula
  _=>_ : Formula → Formula → Formula
  _<=>_ : Formula → Formula → Formula
  _∧_ : Formula → Formula → Formula
  _∨_ : Formula → Formula → Formula
  ForAll : Var → Formula → Formula
  Exists : Var → Formula → Formula

open import Boolean

data Interpretation (M : Set) : Type where
  φ : (Const → M) → ({n : ℕ} → Func n → (Fin n → M) → M) → ({n : ℕ} → Pred n → (Fin n → M) → Bool) → Interpretation M

term : {M : Set} → Interpretation M → (Var → M) → Term → M
term _ ξ (var x) = ξ x
term (φ x x₁ x₂)_ (const x₃) = x x₃
term (φ x x₁ x₂) ξ (x₃ apply x₄) = x₁ x₃ (λ k → term (φ x x₁ x₂) ξ (x₄ k))


postulate
  ⋀ : (I : Set) → (I → Bool) → Bool
  ⋀=> : (I : Set) → (f : I → Bool) → (⋀ I f) == true -> (i : I) → (f i) == true
  =>⋀ : (I : Set) → (f : I → Bool) → ((i : I) → (f i) == true)  → (⋀ I f) == true




bool : {M : Set} → Interpretation M → (Var → M) → Formula → Bool
bool (φ x x₁ x₂) ξ (x₃ apply x₄) = x₂ x₃ (λ k → term (φ x x₁ x₂) ξ (x₄ k))
bool ψ ξ (¬ fmla) = not (bool ψ ξ fmla)
bool ψ ξ (fmla => fmla₁) = not (bool ψ ξ fmla) || bool ψ ξ fmla₁
bool ψ ξ (fmla <=> fmla₁) = (bool ψ ξ fmla & bool ψ ξ fmla₁) ||
                              (not (bool ψ ξ fmla) & not (bool ψ ξ fmla₁))
bool ψ ξ (fmla ∧ fmla₁) = bool ψ ξ fmla & bool ψ ξ fmla₁
bool ψ ξ (fmla ∨ fmla₁) = bool ψ ξ fmla || bool ψ ξ fmla₁
bool {M} ψ ξ (ForAll x fmla) = ⋀ (Σ (Var → M) (λ ζ → (y : Var) → (y == x) ⊕ (ζ y == ξ y))) (λ x₁ → bool ψ (proj₁ x₁) fmla)
bool ψ ξ (Exists x fmla) = {!!}


module Theory (axioms : Formula → Bool) where
  data Model (M : Set) : Type where
    model : (ψ : Interpretation M) → (fmla : Formula) → (axioms fmla == true) → (ξ : Var -> M) → (bool ψ ξ fmla) == true → Model M

  data Deduction : Formula ->  Type where
    assumption : {P : Formula} → (axioms P) == true → Deduction P
    MP : {P Q : Formula} → Deduction P → Deduction (P => Q) → Deduction Q
