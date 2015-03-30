open import Base

open import Homotopy

open import Id

module Equivalence where

data _≅_  {X : Set₁} : X → X → Set₁ where
  refl : (A : X) → A ≅ A

data _≃_ : Type → Type → Set₁ where
  _use_ : {A B : Type} → (f : A → B) → isEquiv(f) → A ≃ B 

≅To≃ : {A B : Type} → (A ≅ B) → A ≃ B
≅To≃ {.B} {B} (refl .B) = id B use idEqv B

Id : (A : Set₁) → A → A
Id A x = x

_∼₁_ : {X Y : Set₁} → (f g : X → Y) → Set₁
_∼₁_ {X} {_} f g = (x : X) → (f(x) ≅ g(x))

data isEquiv₁ {A B : Set₁} : (A → B) → Set₁ where 
  eqv : (f : A → B) → (g : B → A) → (h : B → A) → (Id A ∼₁ (λ x → g (f x))) → (Id B ∼₁ (λ x → f (h x))) → isEquiv₁ f

postulate
  univalence : (A : Type) → (B : Type) → isEquiv₁ {A ≅ B} {A ≃ B} ≅To≃

open import Boolean

flip : Bool ≃ Bool
flip = not use notIsEquiv
