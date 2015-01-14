module FAlg where

data Alg : Set where
  _⊕_ : (t : Alg) → (u : Alg) → Alg
  K1 : Alg
  _⊗_ : (t : Alg) → (u : Alg) → Alg
  
data Val : Alg → Set where
  V1 : Val K1
  _,_ : {t u : Alg} → (a : Val t) → (b : Val u) → Val (t ⊗ u)
  inL : {t u : Alg} → (a : Val t) → Val (t ⊕ u)
  inR : {t u : Alg} → (b : Val u) → Val (t ⊕ u)
  
fstV : {t u : Alg} → Val (t ⊗ u) → Val t
fstV (a , b) = a

sndV : {t u : Alg} → Val (t ⊗ u) → Val u
sndV (a , b) = b

caseV : {t u : Alg} {A : Set} → Val (t ⊕ u) → (Val t → A) → (Val u → A) → A
caseV (inL v) l r = l v
caseV (inR v) l r = r v

