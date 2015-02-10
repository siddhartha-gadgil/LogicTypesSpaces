open import Base

open import Id

module Semigroups where

assoc : {A : Type} → (A → A → A) → Type
assoc {A} (_*_) = (x y z : A) → (x * (y * z)) == ((x * y) * z)

semigroup : Type → Type
semigroup A = Σ (A → A → A) (λ op → assoc op)

module SemiGroup{A : Type}(_·_ : A → A → A)(pf : assoc _·_) where
  leftId : A → Type
  leftId e = (y : A) → (e · y) == y

  rightId : A → Type
  rightId e = (x : A) → (x · e) == x

  idUnique : (p q : A) → (leftId p) → (rightId q) → q == p
  idUnique p q lidp ridq = sym (lidp q) && (ridq p) 

  struct : semigroup A
  struct = [ _·_ , pf ]

open import Nat

assoc+ : assoc _+_
assoc+ zero y z = refl (y + z)
assoc+ (succ x) y z = succ # (assoc+ x y z)

module Nat+ = SemiGroup _+_ assoc+
