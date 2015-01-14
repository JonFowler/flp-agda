module PL where

open import FAlg
open import Data.Nat
open import Data.Fin
open import Data.Vec

Cxt : ℕ → Set
Cxt n = Vec Alg n

data Exp {n : ℕ} (Γ : Cxt n) : Alg → Set where
  val : {t : Alg}  → (a : Val t) → Exp Γ t 
  var : (x : Fin n) → Exp Γ (lookup x Γ) 
  fst : {t u : Alg} → Exp Γ (t ⊗ u) → Exp Γ t 
  snd : {t u : Alg} → Exp Γ (t ⊗ u) → Exp Γ u 
  case : {t u v : Alg} → Exp Γ (t ⊕ u) → 
                          Exp (t ∷ Γ) v → Exp (u ∷ Γ) v → Exp Γ v
--  ƛ : {t u : FAlg} → Exp (t ∷ Γ) u → Exp Γ u

  
data Env : {n : ℕ} → Cxt n → Set where
  [] : Env []
  _∷_ : ∀ {t n} {Γ : Cxt n} → Val t → Env Γ → Env (t ∷ Γ)
  
lookupE :{n : ℕ}{Γ : Cxt n} → (i : Fin n) → Env Γ → Val (lookup i Γ) 
lookupE zero (x ∷ s) = x
lookupE (suc i) (x ∷ s) = lookupE i s
  
eval : ∀ {t n} {Γ : Cxt n} → Exp Γ t  → Env Γ → Val t
eval (val a) s = a
eval (var x) s = lookupE x s
eval (fst e) s = fstV (eval e s)
eval (snd e) s = sndV (eval e s)
eval (case e1 e2 e3) s = caseV (eval e1 s) 
                               (λ x → eval e2 (x ∷ s)) 
                               (λ x → eval e3 (x ∷ s))
--eval (ƛ e) s = {!s!}
  
--eval : ∀ {Γ n} → Exp Γ n →  
