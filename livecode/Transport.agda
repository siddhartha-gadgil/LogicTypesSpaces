open import Base

module Transport where

transport : {A : Type} → {B : A → Type} → {x y : A} → (p : x == y) → B x → B y
transport {A} {B} {.y} {y} (refl .y) = λ a → a 

_##_ : {A : Type} → {B : A → Type} → {x y : A} → (f : (a : A) → B a) → (p : x == y) → (transport p (f x)) == (f y)
_##_ {A} {B} {.y} {y} f (refl .y) = refl (f y)
