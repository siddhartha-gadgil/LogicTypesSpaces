open import Base

module Logic where

data True : Type where
  qed : True

data False : Type where

mp : {P : Type} → {Q : Type} → P → (P → Q) → Q
mp p f = f p

vacuous : (A : Type) → (False → A)
vacuous A ()
