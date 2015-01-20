open import Base

module Option where

data Option (A : Type) : Type where
  Some : A → Option A
  None : Option A

_mapOption_ : {A B : Type} → Option A → (A → B) → Option B
None mapOption f = None
(Some a) mapOption f = Some (f a)

_flatMapOption_ : {A B : Type} → Option A → (A → Option B) → Option B
None flatMapOption _ = None
(Some a) flatMapOption f = f a
