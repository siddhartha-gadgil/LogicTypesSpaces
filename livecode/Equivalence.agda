open import Base

open import Homotopy

open import Id

module Equivalence where

data _≅_ : Type → Type → Set₁ where
  refl : (A : Type) → A ≅ A

data _≃_ : Type → Type → Set₁ where
  _use_ : {A B : Type} → (f : A → B) → isEquiv(f) → A ≃ B 

≅To≃ : {A B : Type} → (A ≅ B) → A ≃ B
≅To≃ {.B} {B} (refl .B) = id B use idEqv B