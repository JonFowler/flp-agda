module FAlg where

data FAlg : Set 
data SAlg : Set where
  _⊕_ : (t : FAlg) → (u : FAlg) → SAlg
  K1 : SAlg
  
data FAlg where
  _⊗_ : (t : FAlg) → (u : FAlg) → FAlg
  In : SAlg → FAlg
  
data FVal : FAlg → Set where
  V1 : FVal (In K1)
  _,_ : {t u : FAlg} → (a : FVal t) → (b : FVal u) → FVal (t ⊗ u)
  inL : {t u : FAlg} → (a : FVal t) → FVal (In (t ⊕ u))
  inR : {t u : FAlg} → (b : FVal u) → FVal (In (t ⊕ u))
  
fstV : {t u : FAlg} → FVal (t ⊗ u) → FVal t
fstV (a , b) = a

sndV : {t u : FAlg} → FVal (t ⊗ u) → FVal u
sndV (a , b) = b

caseV : {t u : FAlg} {A : Set} → FVal (In (t ⊕ u)) → (FVal t → A) → (FVal u → A) → A
caseV (inL v) l r = l v
caseV (inR v) l r = r v

