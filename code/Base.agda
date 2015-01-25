module Base where

Type : Set₁
Type = Set

data _×_ (A B : Type) : Type where
  [_,_] : A → B → A × B

data _⊕_ (A B : Type) : Type where
  ι₁ : A → A ⊕ B
  ι₂ : B → A ⊕ B

data Σ (A : Type) (B : A → Type) : Type where
 [_,_] : (a : A) → (B a) → Σ A B
 
