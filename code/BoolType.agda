module BoolType where


data Bool : Set where
  true   : Bool
  false  : Bool


not : Bool -> Bool
not true = false
not false = true


_&_ : Bool → Bool → Bool
true & true = true
false & _ = false
true & false = false


notnot : Bool -> Bool
notnot x = not (not x)


verytrue : Bool → Bool
verytrue = λ x → x & x


_||_ : Bool → Bool → Bool
false || false = false
true  || _ = false
false || true = true
 

_xor_ : Bool → Bool → Bool
_xor_ = λ x y → (x & (not y)) || ((not x) & y)










