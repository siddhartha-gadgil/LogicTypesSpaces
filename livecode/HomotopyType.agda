
open import Base

open import Homotopy

module HomotopyType where

data BasedType : Set₁ where
  [_,_] : (A : Type) → A → BasedType

space : BasedType → Type
space [ A , _ ] = A

point : (Aa : BasedType) → (space Aa)
point [ _ , a ] = a


isContractible : BasedType → Type
isContractible Aa = (x : (space Aa)) → (x == (point Aa))

open import Nat

data _hasLevel_-1 : (A : Type) → (n : ℕ) → Set₁ where
  base : (Aa : BasedType) → isContractible Aa → (space Aa) hasLevel 0 -1
  deloop : {n : ℕ} → (A : Type) → ((x : A) → (y : A) → (x == y) hasLevel n -1) → A hasLevel (succ n) -1 

loopSpace : BasedType → BasedType
loopSpace Aa = [ (a == a) , refl a ] where
  a = point Aa


contractLoop : (Aa : BasedType) →  (l : (point Aa) == (point Aa)) → l == (refl (point Aa))
contractLoop Aa (refl .(point Aa)) = refl (refl (point Aa))

loopSpcContract : (Aa : BasedType)  → isContractible (loopSpace Aa)
loopSpcContract Aa  = λ (x : point Aa == point Aa) → contractLoop Aa  x
