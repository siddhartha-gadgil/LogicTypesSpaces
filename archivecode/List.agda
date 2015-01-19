module List where

Type : Set₁
Type = Set

data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A


open import Nat

onetwothree : List ℕ
onetwothree = 1 :: (2 :: (3 :: []))



-- Length of a list, first attempt
length₀ : (A : Set) → List A → ℕ
length₀ _ [] = zero
length₀ A (a :: l) = succ (length₀ A l)


-- Length of a list with implicit parameter
length : {A : Set} → List A → ℕ
length [] = zero
length (a :: l) = succ (length l)

_++_ : {A : Set} → List A → List A → List A
[] ++ l = l
(a :: xs) ++ l = a :: (xs ++ l)

reverse : {A : Set} → List A → List A
reverse [] = []
reverse (a :: l) = (reverse l) ++ (a :: [])


_map_ : {A B : Set} → List A → (A → B) → List B
[] map _ = []
(a :: xs) map f = (f a) :: (xs map f)


 
_flatMap_ : {A B : Set} → List A → (A → List B) → List B
[] flatMap _ = []
(a :: xs) flatMap f = (f a) ++ (xs flatMap f)


twothreefour : List ℕ
twothreefour = onetwothree map succ
