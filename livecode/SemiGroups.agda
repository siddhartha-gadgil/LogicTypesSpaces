open import Base

open import Id

module SemiGroups where

test : Type → Type
test A = (a : A) → (a == a)

assoc : {A : Type} → (A → A → A) → Type
assoc {A} _*_ = (x : A) → (y : A) → (z : A) → ((x * y) * z) == (x * (y * z))

semiGroup : (A : Type) → Type
semiGroup A = Σ (A → A → A) (λ op → assoc op) 

module SemiGroup(A : Type)(_·_ : A → A → A)(ass : (assoc _·_)) where
  leftId : A → Type
  leftId x = (y : A) → ((x · y) == y)

  rightId : A → Type
  rightId x = (y : A) → ((y · x) == y)

  Id = λ a → (leftId a) × (rightId a)

  idUnique : (x y : A) → leftId x → rightId y → y == x
  idUnique x y lidx ridy = sym (lidx y) && ridy x

open import Nat

ass+ : assoc _+_
ass+ zero y z = refl (y + z)
ass+ (succ x) y z = succ # ass+ x y z

module AddNatSG = SemiGroup ℕ _+_ ass+




