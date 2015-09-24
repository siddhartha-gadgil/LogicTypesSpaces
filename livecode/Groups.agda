open import Base
open import Id


module Groups where

assoc : {A  : Type} → (A → A → A) → Type
assoc {A} _*_ = (x y z : A) → ((x * y) * z) == (x * (y * z))

comm : {A : Type} → (A → A → A) → Type
comm {A} _*_ = (x y : A) → (x * y) == (y * x)

Id : {A : Type} → (A → A → A) → A → Type
Id {A} _*_ e = (x : A) →  ((e * x) == x) × ((x * e) == x)

Inv : {A : Type} → (A → A → A) → A → Type
Inv {A} _*_ id = (x : A) → Σ A (λ y → (((y * x) == id) × ((x * y) == id)))

  

module Group(A : Type)(_·_ : A → A → A)(pfassoc : assoc _·_) (e : A) (pfid : Id _·_ e) (pfinv : Inv _·_ e) where 
 Id! : (e' : A) → ( Id _·_ e') → (e' == e)
 Id! e' pf =( sym (p₁(pfid e')) && (p₂(pf e)))

 --inv : (x : A) → ((y : A) × (((y · x) == e) × ((x · y) == e))) 
 --inv x = ?



 Inv! : {x x₁ x₂ : A} → ((x₁ · x) == e) → ((x · x₂) == e)  → (x₁ == x₂)
 Inv! {x} {x₁} {x₂} a b = (sym(p₂(pfid x₁))) 
   &&  ((λ m → (x₁ · m)) # (sym b)) 
   && (sym(pfassoc x₁ x x₂)) 
   && ((λ m → m · x₂) # a) 
   && p₁ (pfid x₂)

 r=l : {x y z : A} → ((x · y) == e) → ((z · x) == e) → (z == y)
 r=l {x} {y} {z} pf₁ pf₂ =  (sym(p₂(pfid z))) 
   && ((λ t → z · t) # sym pf₁ 
   && (sym (pfassoc z x y) 
   && ((λ t → t · y) # pf₂ 
   && p₁ (pfid y))))

 cancl : {a b c ainv : A} → ((a · b) ==  (a · c)) → ((ainv · a) == e) → (b == c)
 cancl {a} {b} {c} {ainv} pf₁ pf₂ = (sym(p₁(pfid b))) 
   && ((λ t → t · b) # sym pf₂)
   && (pfassoc ainv a b) 
   && ((λ t → ainv · t) # pf₁) 
   && (sym(pfassoc ainv a c)) 
   && ((λ t → t · c) # pf₂)
   && (p₁(pfid c))

 cancr : {a b c ainv : A} → ((b · a) ==  (c · a)) → ((a · ainv) == e) → (b == c)
 cancr {a} {b} {c} {ainv} pf₁ pf₂ = (sym(p₂(pfid b))) 
   && ((λ t → b · t) # sym pf₂)
   && (sym(pfassoc b a ainv)) 
   && ((λ t → t · ainv) # pf₁) 
   && (pfassoc c a ainv) 
   && ((λ t → c · t) # pf₂)
   && (p₂(pfid c))

 compinv : {a b x ainv binv : A} → ((x · (a · b)) == e) → ((a · ainv) == e) → ((b · binv) == e) → (x == (binv · ainv))
 compinv {a} {b} {x} {ainv} {binv} pf₁ pf₂ pf₃ = (sym(p₂(pfid(x)))) 
   && (λ t → x · t) # sym pf₂  
   && (sym (pfassoc x a ainv) )
   && ((λ t → (x · a) · t) # sym (p₁ (pfid ainv)))
   && ((λ t → (x · a) · (t · ainv)) # sym pf₃) 
   && ((λ t → (x · a) · t) # pfassoc b binv ainv)
   && (sym (pfassoc (x · a) b (binv · ainv)) )
   && ((λ t → t · (binv · ainv)) # pfassoc x a b) 
   && ((λ t → t · (binv · ainv)) # pf₁)
   && p₁ (pfid (binv · ainv))



 --cinv : {a b ainv binv : A} → ((a ainv) == e) → (())


--data B : Type where
--  I : Groups.Group --(A : Type)(_·_ : A → A → A)(pfassoc : assoc _·_) (e : A) (pfid : Id _·_ e) (pfinv : Inv _·_ e)


--data GrpHom : {A : Type} → {_._ : A → A → A} → {pfassoc : assoc _·_} --→ {e : A} → {pfid : Id _·_ e} →  {pfinv : Inv _·_ e} → (G H : Group A _·_ pfassoc e pfid  pfinv)  → Type where
  