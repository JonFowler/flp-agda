module SubAdv where

open import FAlg


data Sub : Alg → Set where
  _,_ : ∀{t u} → Sub t → Sub u → Sub (t ⊗ u)
  V1 : Sub K1
  hole : ∀{t} → Sub t
  
data Pos  : {t : Alg} → Sub t → Set where
  here : ∀{t} → Pos {t} hole
  infst : ∀{t u}{a : Sub t}{b : Sub u} → Pos a → Pos (a , b)
  insnd : ∀{t u}{a : Sub t}{b : Sub u} → Pos b → Pos (a , b)

data RealSub : {t : Alg} → Sub t → Set where
  
