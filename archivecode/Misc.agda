module Misc where

data 𝟘 : Set where

data 𝟙 : Set where
  * : 𝟙

data _×_ (A B : Set) : Set where 
  [_,_] : A → B → A × B

data _⊕_ (A B : Set) : Set where
  ι₁ : A → A ⊕ B
  ι₂ : B → A ⊕ B
