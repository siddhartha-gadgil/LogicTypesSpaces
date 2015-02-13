module Id where

open import Base

sym : {A : Type} → {x y : A} → (x == y) → (y == x)
sym (refl a) = refl a

_&&_ : {A : Type} → {x y z : A} → (x == y) → (y == z) → (x == z)
(refl a) && (refl .a) = refl a


_#_ : {A B : Type} → {x y : A} → (f : A → B) → (x == y) → ((f x) == (f y))
f # (refl a) = refl (f a)

postulate
  extensionality : {A B : Type} → (f g : A → B) → ((x : A) → ((f x) == (g x))) → f == g
