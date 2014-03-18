open import Nat

module Vect where

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

countdown : (n : ℕ) → Vec ℕ n
countdown zero = []
countdown (succ m) = (succ m) :: (countdown m)


{- Polvectors have different types for different terms.
They are built by appending from the empty Polyvector.
Indices start with 0 and the ith term has type (As i)
-}
data PolyVec (As : ℕ → Set) : ℕ → Set where
  []   : PolyVec As zero
  _:+_ : {n : ℕ} → PolyVec As n → As n → PolyVec As (succ n)
