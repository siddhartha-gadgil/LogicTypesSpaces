open import Base

open import Nat

module List where


data List (A : Type) : Type where
  [] : List A
  _::_ : A → List A → List A

data AnotherList (A : Type) : Type where
  [] : AnotherList A
  _:::_ : AnotherList A → A → AnotherList A


onetwothree : List ℕ
onetwothree = 1 :: (2 :: (3 :: []))

threetwo = ([] ::: 3) ::: 2 

length₀ : (A : Type) → List A → ℕ
length₀ A [] = 0
length₀ A (a :: l) = succ (length₀ A l)

length : {A : Type} → List A → ℕ
length [] = 0
length (a :: l) = succ (length l)

onN : List ℕ → ℕ
onN [] = 1
onN (a :: l) = (onN l) * 2 

_++_ : {A : Type} → List A → List A → List A
[] ++ l = l
(x :: ys) ++ zs = x :: (ys ++ zs)

reverse : {A : Type} → List A → List A
reverse [] = []
reverse (x :: ys) = (reverse ys) ++ (x :: [])

_map_ : {A B : Type} → List A → (A → B) → List B
[] map f = []
(x :: ys) map f = (f x) :: (ys map f)

ofn : List ℕ
ofn = onetwothree map (λ x → x * x)

ffs = onetwothree map (_+_ 3)

_flatMap_ : {A B : Type} → List A → (A → List B) → List B
[] flatMap _ = []
(x :: ys) flatMap f = (f x) ++ (ys flatMap f)

open import Boolean

_contains_ : {A : Type} → List A → (A → Bool) → Bool
[] contains _ = false
(x :: ys) contains p = (p x) || (ys contains p)

_filter_ : {A : Type} → List A → (A → Bool) → List A
[] filter _ = []
(x :: ys) filter p = if (p x) then (x :: (ys filter p)) else (ys filter p)

fold_by_from_ : {A B : Type} → List A → (A → B → B) → B → B
fold [] by _ from b = b
fold (x :: ys) by op from b = op x (fold ys by op from b) 

open import Option

_find_ : {A : Type} → List A → (A → Bool) → Option A
[] find _ = None
(x :: ys) find p = if (p x) then (Some x) else (ys find p) 
