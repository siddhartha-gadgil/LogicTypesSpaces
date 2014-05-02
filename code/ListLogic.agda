open import BoolType

open import List

module ListLogic where

_contains_ : {A : Set} → List A → (A → Bool) → Bool
[] contains _ = false
(x :: xs) contains p = (p x) || (xs contains p)


if_then_else : {A : Set} → Bool → A → A  → A
if true then x else _ = x
if false then _ else y = y

_filter_ : {A : Set} → List A → (A → Bool) → List A
[] filter _ = []
(x :: xs) filter p = if (p x) then (x :: (xs filter p)) else (xs filter p)


fold_by_from_ : {A : Set} → {B : Set} → List A → (A → B → B) → B → B
fold [] by _ from b = b
fold (x :: xs) by op from b = op x (fold xs by op from b)

open import Nat

upto : ℕ → List ℕ
upto zero = []
upto (succ n) = (upto n) ++ ((succ n) :: [])

listsqs : ℕ → List ℕ
listsqs n = upto n map (λ x → (x * x))

sumsqs : ℕ → ℕ
sumsqs n = fold (listsqs n) by _+_ from zero


data Option (A : Set) : Set where
  Some : A → Option A
  None : Option A


_find_ : {A : Set} → List A → (A → Bool) → Option A
[] find _ = None
(x :: xs) find p = if (p x) then (Some x) else (xs find p)


_mapOption_ : {A : Set} → {B : Set} → Option A → (A → B) → Option B
None mapOption _ = None
(Some a) mapOption f = Some (f a)

_flatMapOption_ : {A : Set} → {B : Set} → Option A → (A →  Option B) → Option B
None flatMapOption _ = None
(Some a) flatMapOption f = f a



