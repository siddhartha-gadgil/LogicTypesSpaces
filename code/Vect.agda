open import Nat

module Vect where

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

_:+_ : {A : Set} → {n : ℕ} → A → Vec A n → Vec A (succ n)
a :+ [] = a :: []
a :+ (x :: xs) = x :: (a :+ xs)


countdown : (n : ℕ) → Vec ℕ (succ n)
countdown zero = zero :: []
countdown (succ m) = (succ m) :: (countdown m)


{- Polvectors have different types for different terms.
They are built by appending from the empty Polyvector.
Indices start with 0 and the ith term has type (As i)
-}
data PolyVec (As : ℕ → Set) : ℕ → Set where
  []   : PolyVec As zero
  _::+_ : {n : ℕ} → PolyVec As n → As n → PolyVec As (succ n)


zipop : {A : Set} → {n : ℕ} → Vec A n → Vec A n → (A → A → A) → Vec A n
zipop  [] [] _ = []
zipop  (x :: xs) (y :: ys) op = (op x y) :: (zipop  xs ys op)

head : {A : Set} → {n : ℕ} → Vec A (succ n) → A
head (x :: xs) = x

_vmap_ : {A B : Set} → {n : ℕ} → Vec A n → (A → B) → Vec B n
[] vmap _ = []
(x :: xs) vmap f = (f x) :: (xs vmap f)


 
length : {A : Set} → {n : ℕ} → Vec A n → ℕ
length {A} {n} v = n

eglength : ℕ → ℕ
eglength n = length (countdown n)

