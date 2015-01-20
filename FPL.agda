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
  infst : {t u r : Alg}{a : FCxt t}{b : FCxt u} → (x : FVar a r) → FVar (a , b) r
  insnd : {t u r : Alg}{a : FCxt t}{b : FCxt u} → (x : FVar b r) → FVar (a , b) r
  inL : {t u r : Alg} {a : FCxt t} → (x : FVar a r) → FVar {t ⊕ u} (inL a) r
  inR : {t u r : Alg} {a : FCxt u} → (x : FVar a r) → FVar {t ⊕ u} (inR a) r

data ExpF {n : ℕ} {s : Alg} (Γ : Cxt n) (Δ : FCxt s) (t : Alg) : Set 

data ValF {n : ℕ} {t : Alg} (Γ : Cxt n) (Δ : FCxt t) : Alg → Set where
     V1 : ValF Γ Δ K1
     _,_ : {t u : Alg} → ExpF Γ Δ t → ExpF Γ Δ u → ValF Γ Δ (t ⊗ u)
     inL : {t u : Alg} → ExpF Γ Δ t → ValF Γ Δ (t ⊕ u)
     inR : {t u : Alg} → ExpF Γ Δ u → ValF Γ Δ (t ⊕ u)
  
--_[_] : (t : FCxt) → (v : FVar t) →  Alg
--_[_] t here = t
--_[_] (t ⊗ _) (inFst v) = t [ v ]
--_[_] (_ ⊗ u) (inSnd v) = u [ v ]

data ExpF {n : ℕ} {s : Alg} (Γ : Cxt n) (Δ : FCxt s) (t : Alg) where
  val : (a : ValF Γ Δ t) → ExpF Γ Δ t 
  var : (v : Fin n) → (p : Γ [ v ]= t)  → ExpF Γ Δ t 
  fvar : (x : FVar Δ t) → ExpF Γ Δ t 
  fst : {u : Alg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
  snd : {u : Alg} → ExpF Γ Δ (u ⊗ t) → ExpF Γ Δ t
  case : {u v : Alg} → ExpF Γ Δ (u ⊕ v) → 
                  ExpF (u ∷ Γ) Δ t → ExpF (v ∷ Γ) Δ t → ExpF Γ Δ t

