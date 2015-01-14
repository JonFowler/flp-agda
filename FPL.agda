module FPL where

open import FAlg
open import PL
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding ([_])

FCxt : Set
FCxt = FAlg

data FVar : FCxt → Set where
  here : {t : FCxt} → FVar t
  inFst : {t u : FCxt} → FVar t → FVar (t ⊗ u)
  inSnd : {t u : FCxt} → FVar u → FVar (t ⊗ u)
  
_[_] : (t : FCxt) → (v : FVar t) →  FAlg
_[_] t here = t
_[_] (t ⊗ _) (inFst v) = t [ v ]
_[_] (_ ⊗ u) (inSnd v) = u [ v ]

data ExpF {n : ℕ} (Γ : Cxt n) : FCxt → FAlg → Set where
  val : {Δ : FCxt}{t : FAlg}  → (a : FVal t) → ExpF Γ Δ t 
  var : {Δ : FCxt}(x : Fin n) → ExpF Γ Δ (lookup x Γ) 
  fvar : {Δ : FCxt}(x : FVar Δ) → ExpF Γ Δ (Δ [ x ]) 
  fst : {Δ : FCxt}{t u : FAlg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
  snd : {Δ : FCxt}{t u : FAlg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ u 
  case : {Δ : FCxt}{t u v : FAlg} → ExpF Γ Δ (In (t ⊕ u)) → 
                  ExpF (t ∷ Γ) Δ v → ExpF (u ∷ Γ) Δ v → ExpF Γ Δ v

