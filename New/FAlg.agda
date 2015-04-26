module FAlg where

data Alg : Set where
--  _⊕_ : (t : Alg) → (u : Alg) → Alg
  K1 : Alg
  _⊗_ : (t : Alg) → (u : Alg) → Alg
  
data ValG (P : Alg → Set) : Alg → Set where
  V1 : ValG P K1
  _,_ : {t u : Alg} → (a : P t) → (b : P u) → ValG P (t ⊗ u)
--  inL : {t u : Alg} → (a : PVal t) → PVal (t ⊕ u)
--  inR : {t u : Alg} → (b : PVal u) → PVal (t ⊕ u)
  
--fstV : {t u : Alg} → PVal (t ⊗ u) → PVal t
--fstV (a , b) = a
--
--sndV : {t u : Alg} → PVal (t ⊗ u) → PVal u
--sndV (a , b) = b
--
--caseV : {t u : Alg} {A : Set} → PVal (t ⊕ u) → (PVal t → A) → (PVal u → A) → A
--caseV (inL v) l r = l v
--caseV (inR v) l r = r v

