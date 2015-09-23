open import Base

module Boolean where


data Bool : Type where 
  true : Bool
  false : Bool

not : Bool → Bool
not true = false
not false = true

thisIsFalse : Bool
thisIsFalse = not(true)

and : Bool -> (Bool -> Bool)
and true true = true
and false _ = false
and true false = false

_&_ : Bool → Bool → Bool
true & true = true
false & _ = false
true & false = false

_&&_ : Bool → Bool → Bool
_&&_ = and

thisIsTrue : Bool
thisIsTrue = _&_ true true

verytrue : Bool → Bool
verytrue x = x & x

notnot : Bool → Bool
notnot = λ x → not (not x)

_||_ : Bool → Bool → Bool
true || _ = true
false || y = y

_xor_ : Bool → Bool → Bool
_xor_ = λ x y → (x || y) & not (x & y)

xor₀ : Bool → Bool → Bool
xor₀ = λ x → (λ y → (x || y) & not (x & y))

xor₁ : Bool → Bool → Bool
xor₁ x y = (x || y) & not (x & y)

if_then_else_ : {A : Type} → Bool → A → A → A
if true then x else y = x
if false then x else y = y 
