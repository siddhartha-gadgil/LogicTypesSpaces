open import Base
open import Id

module Homotopy where

_∼_ : {X Y : Type} → (f g : X → Y) → Type
_∼_ {X} {_} f g = (x : X) → (f(x) == g(x))

_~_ : {X : Type} → {Y : X → Type} → (f g : ((x : X) → (Y x))) → Type
_~_ {X} {_} f g = (x : X) → (f(x) == g(x))

rfl : {X Y : Type} → (f : X → Y) → (f ∼ f)
rfl {X} {_} f = λ x → (refl (f x))

symm : {X Y : Type} → (f g : X → Y) → (f ∼ g) → (g ∼ f)
symm {X} {_} f g pf = λ x → (sym (pf x))

_trans_ : {X Y : Type} → (f g h : X → Y) → (f ∼ g) → (g ∼ h) → (f ∼ h)
_trans_ {X} {_} f g h f∼g g∼h = λ x → (f∼g x) && (g∼h x)


_∘id : {X Y : Type} → (f : X → Y) → ((f ∘ (id X)) ∼ f)
_∘id {X} {_} f = λ x → (refl (f x))

id∘_ : {X Y : Type} → (f : X → Y) → (((id Y) ∘ f ) ∼ f)
id∘_ {X} {_} f = λ x → (refl (f x))



isQuasiEquiv : {X Y : Type} → (X → Y) → Type
isQuasiEquiv {X} {Y} f = Σ (Y → X) (λ g → ((f ∘ g) ∼ (id Y)) × ((g ∘ f) ∼ (id X)))

isEquiv : {X Y : Type} → (X → Y) → Type
isEquiv {X} {Y} f = Σ (Y → X) (λ h → Σ (Y → X) (λ g → ((f ∘ g) ∼ (id Y)) × ((h ∘ f) ∼ (id X))))
 
idEqv : (A : Type) → isEquiv (id A)
idEqv A = [ (id A) , [ (id A) , [ (rfl (id A)) , (rfl (id A)) ] ] ]


QImonodromy : (X : Type) → isQuasiEquiv (id X)  → ((x : X) → (x == x)) 
QImonodromy X qe x = (sym ((p₁ (proj₂ qe)) x)) && p₂ (proj₂ qe) x


open import Boolean

notnot~id : (not ∘ not) ~ (id Bool)
notnot~id true = refl true
notnot~id false = refl false

notIsEquiv : isEquiv(not)
notIsEquiv = [ not , [ not ,  [ notnot~id , notnot~id ]  ] ]
