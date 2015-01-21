module FPL where

open import FAlg 
open import PL
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product
open import Data.Vec hiding ([_])

data Test : Alg → Set where
  test : {t : Alg} → ValG Test t → Test t 
  free : {u t : Alg} → Test (u ⊕ t)


data FCxt : Alg → Set where
  V1 : FCxt K1
  _,_ : {t u : Alg} → (a : FCxt t) → (b : FCxt u) → FCxt (t ⊗ u)
  fvar : {t u : Alg} → FCxt (t ⊕ u)
  inL : {t u : Alg} → (a : FCxt t) → FCxt (t ⊕ u)
  inR : {t u : Alg} → (a : FCxt u) → FCxt (t ⊕ u)
  
testf : {t : Alg} → Test t → FCxt t
testf (test V1) = V1
testf (test (a , b)) = testf a , testf b
testf (test (inL a)) = inL (testf a) 
testf (test (inR b)) = inR (testf b) 
testf free = fvar
  
data FVar : {t : Alg} → FCxt t → Alg → Set where
  here : {t : Alg} {x : FCxt t} → FVar x t
  infst : {t u r : Alg}{a : FCxt t}{b : FCxt u} → (x : FVar a r) → FVar (a , b) r
  insnd : {t u r : Alg}{a : FCxt t}{b : FCxt u} → (x : FVar b r) → FVar (a , b) r
  inL : {t u r : Alg} {a : FCxt t} → (x : FVar a r) → FVar {t ⊕ u} (inL a) r
  inR : {t u r : Alg} {a : FCxt u} → (x : FVar a r) → FVar {t ⊕ u} (inR a) r

--data ExpF {n : ℕ} {s : Alg} (Γ : Cxt n) (Δ : FCxt s) (t : Alg) : Set 
--
--data ValF {n : ℕ} {t : Alg} (Γ : Cxt n) (Δ : FCxt t) : Alg → Set where
--     V1 : ValF Γ Δ K1
--     _,_ : {t u : Alg} → ExpF Γ Δ t → ExpF Γ Δ u → ValF Γ Δ (t ⊗ u)
--     inL : {t u : Alg} → ExpF Γ Δ t → ValF Γ Δ (t ⊕ u)
--     inR : {t u : Alg} → ExpF Γ Δ u → ValF Γ Δ (t ⊕ u)
  
--data ExpF {n}{s} Γ Δ t where
--  val : (a : ValF Γ Δ t) → ExpF Γ Δ t 
--  var : (v : Fin n) → (p : Γ [ v ]= t)  → ExpF Γ Δ t 
--  varF : (x : FVar Δ t) → ExpF Γ Δ t 
--  fst : {u : Alg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
--  snd : {u : Alg} → ExpF Γ Δ (u ⊗ t) → ExpF Γ Δ t
--  case : {u v : Alg} → ExpF Γ Δ (u ⊕ v) → 
--                  ExpF (u ∷ Γ) Δ t → ExpF (v ∷ Γ) Δ t → ExpF Γ Δ t
--
--data _[_]:=_ {n : ℕ}{Γ : Cxt n} : {t : Alg} (Δ : FCxt t) → FVar Δ t → ValF Γ Δ t → Set where
--  hereV1 : V1 [ here ]:= V1
--  here, : {u v : Alg} {a : FCxt u} {b : FCxt v} → 
--      (a , b) [ here ]:= ( varF (infst here) , varF (insnd here) )
--  hereL : {u v : Alg} {a : FCxt u} → inL {u = v} a [ here ]:= inL (varF (inL here))
