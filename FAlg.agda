module FAlg where

open import Data.Product
open import Data.Empty 
open import Relation.Nullary

data FAlg : Set where
  _⊕_ : (t : FAlg) → (u : FAlg) → FAlg
  _⊗_ : (t : FAlg) → (u : FAlg) → FAlg
  K1 : FAlg
  
data FVal : FAlg → Set where
  V1 : FVal K1
  _,_ : {t u : FAlg} → (a : FVal t) → (b : FVal u) → FVal (t ⊗ u)
  inL : {t u : FAlg} → (a : FVal t) → FVal (t ⊕ u)
  inR : {t u : FAlg} → (b : FVal u) → FVal (t ⊕ u)
  
fst : {t u : FAlg} → FVal (t ⊗ u) → FVal t
fst (a , b) = a

snd : {t u : FAlg} → FVal (t ⊗ u) → FVal u
snd (a , b) = b

case : {t u : FAlg} {A : Set} → FVal (t ⊕ u) → (FVal t → A) → (FVal u → A) → A
case (inL v) l r = l v
case (inR v) l r = r v

