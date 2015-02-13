open import Base

open import Nat

module Vector where

data Vec (A : Type) : ℕ → Type where
  [] : Vec A zero
  _::_ : {n : ℕ} → A → Vec A n → Vec A (succ n)

dim : {A : Type} → {n : ℕ} → Vec A n → ℕ
dim [] = 0
dim (head :: tail) = succ (dim tail) 

countdown : (n : ℕ) → Vec ℕ (succ n)
countdown zero = 0 :: []
countdown (succ n) = (succ n) :: countdown n

zip : {A : Type} → {n : ℕ} → Vec A n → Vec A n → Vec (A × A) n
zip [] [] = []
zip (a :: as) (b :: bs) = ([ a , b ]) :: (zip as bs)

-- wrong
-- zip {ℕ} {3} (countdown 2) (countdown 3)

vhead : {A : Type} → {n : ℕ} → Vec A (succ n) → A
vhead (x :: v) = x

vtail : {A : Type} → {n : ℕ} → Vec A (succ n) → Vec A n
vtail (x :: v) = v

open import List

list→vec : {A : Type} → List A → Σ ℕ (λ n → Vec A n)
list→vec [] = [ 0 , [] ]
list→vec (head :: tail) = [ succ (proj₁ (list→vec tail)) , head :: (proj₂ (list→vec tail)) ]

vec→list : {A : Type} → Σ ℕ (λ n → Vec A n) → List A
vec→list [ 0 , [] ] = []
vec→list [ succ n , (head :: tail) ] = head :: (vec→list [ n , tail ])

ltov : {A : Type} → (l : List A) → Vec A (length l)
ltov [] = []
ltov (x :: l) = x :: ltov l

lookup : {A : Type} → (n : ℕ) → Vec A n → (k : ℕ) → (succ k ≤ n) → A
lookup .0 [] k ()
lookup (succ n) (x :: v) zero p = x
lookup (succ n) (x :: v) (succ k) (succ≤ p) = lookup n v k p  

example = lookup _ (1 :: (2 :: (3 :: []))) 1 (succ≤ (succ≤ (0≤ 1)))

-- letstry = lookup _ (1 :: (2 :: (3 :: []))) 1 _


