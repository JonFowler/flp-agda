module FPL where

open import FAlg 
open import PL
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_])

data FCxt : Alg → Set where
  V1 : FCxt K1
  _,_ : {t u : Alg} → (a : FCxt t) → (b : FCxt u) → FCxt (t ⊗ u)
  fvar : {t u : Alg} → FCxt (t ⊕ u)
  inL : {t u : Alg} → (a : FCxt t) → FCxt (t ⊕ u)
  inR : {t u : Alg} → (a : FCxt u) → FCxt (t ⊕ u)
  
data FVar : {t : Alg} → FCxt t → Alg → Set where
  here : {t : Alg} {x : FCxt t} → FVar x t
  infst : {t u r : Alg} {a b : FCxt t} → (x : FVar a r) → FVar (a , b) r
  insnd : {t u r : Alg} {a b : FCxt t} → (x : FVar b r) → FVar (a , b) r
  inL : {t u r : Alg} {a : FCxt t} → (x : FVar a r) → FVar {t ⊕ u} (inL a) r
  inR : {t u r : Alg} {b : FCxt u} → (x : FVar b r) → FVar {t ⊕ u} (inR b) r

data FVal {t : Alg} (Δ : FCxt t) : Alg → Set where
     V1 : FVal Δ K1
     fvar : {u : Alg} → FVar Δ u → FVal Δ u
     _,_ : {t1 t2 : Alg} → FVal Δ t1 → FVal Δ t2 → FVal Δ (t1 ⊗ t2)
  
--_[_] : (t : FCxt) → (v : FVar t) →  Alg
--_[_] t here = t
--_[_] (t ⊗ _) (inFst v) = t [ v ]
--_[_] (_ ⊗ u) (inSnd v) = u [ v ]

--data ExpF {n : ℕ} (Γ : Cxt n) : FCxt → Alg → Set where
--  val : {Δ : FCxt}{t : Alg}  → (a : FVal t) → ExpF Γ Δ t 
--  var : {Δ : FCxt}(x : Fin n) → ExpF Γ Δ (lookup x Γ) 
--  fvar : {Δ : FCxt}(x : FVar Δ) → ExpF Γ Δ (Δ [ x ]) 
--  fst : {Δ : FCxt}{t u : FAlg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
--  snd : {Δ : FCxt}{t u : FAlg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ u 
--  case : {Δ : FCxt}{t u v : FAlg} → ExpF Γ Δ (In (t ⊕ u)) → 
--                  ExpF (t ∷ Γ) Δ v → ExpF (u ∷ Γ) Δ v → ExpF Γ Δ v

