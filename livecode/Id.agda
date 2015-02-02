open import Base

module Id where

sym : {A : Type} → {x y : A} → x == y → y == x
sym (refl x) = refl x

_&&_ : {A : Type} → {x y z : A} → x == y → y == z  → x == z
_&&_ (refl a) (refl .a) = refl a 

_#_ : {A B : Type} → {x y : A} → (f : A → B) → x == y → (f x) == (f y)
f # (refl x) = refl (f x) 


