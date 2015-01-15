module PL where

open import FAlg
open import Data.Nat
open import Data.Fin
open import Data.Vec hiding (_>>=_)
open import Data.Empty
open import Data.Product 

Cxt : ℕ → Set
Cxt n = Vec Alg n

--data _×_ : Set → Set → Set1 where
--  _,_ : ∀ {A B} → (a : A) → (b : B) → A × B


data Exp {n : ℕ} (Γ : Cxt n) : Alg → Set

data Val {n : ℕ} (Γ : Cxt n) : Alg → Set where
  V1 : Val Γ K1
  _,_ : {t u : Alg} → (a : Exp Γ t) → (b : Exp Γ u) → Val Γ (t ⊗ u)
  inL : {t u : Alg} → (a : Exp Γ t) → Val Γ (t ⊕ u)
  inR : {t u : Alg} → (b : Exp Γ u) → Val Γ (t ⊕ u)
 
data Exp {n : ℕ} (Γ : Cxt n) where
  val : {t : Alg}  → (a : Val Γ t) → Exp Γ t 
  var : (x : Fin n) → Exp Γ (lookup x Γ) 
  fst : {t u : Alg} → Exp Γ (t ⊗ u) → Exp Γ t 
  snd : {t u : Alg} → Exp Γ (t ⊗ u) → Exp Γ u 
  case : {t u v : Alg} → Exp Γ (t ⊕ u) → 
                          Exp (t ∷ Γ) v → Exp (u ∷ Γ) v → Exp Γ v
--  ƛ : {t u : FAlg} → Exp (t ∷ Γ) u → Exp Γ u

 
data Env : {n : ℕ} → Cxt n → Set where
  [] : Env []
  _∷_ : ∀ {t n} {Γ : Cxt n} → Exp Γ t → Env Γ → Env (t ∷ Γ)
  
  
cxt-sub : {n : ℕ} → (i : Fin n) → Cxt n → Cxt (n ℕ-ℕ (suc i))
cxt-sub zero (x ∷ Γ) = Γ 
cxt-sub (suc i) (x ∷ Γ) = cxt-sub i Γ
  
lookupE : {n : ℕ}{Γ : Cxt n} → (i : Fin n) → Env Γ → Exp (cxt-sub i Γ) (lookup i Γ) 
lookupE zero (x ∷ s) = x 
lookupE (suc i) (x ∷ s) = lookupE i s

State : Set → Set → Set
State S A = S → (A × S)

_>>=_ : ∀ {S A B} → State S A → (A → State S B) → State S B
f >>= g = λ s → let (a , s') = f s in g a s'
  
eval : ∀ {t n} {Γ : Cxt n} → Exp Γ t  → State (Env Γ) (Val Γ t)  
eval (val a) s = a , s 
eval (var x) s = {!eval (lookupE x s) >>= ?!} 
eval (fst e) s = {!!}
eval (snd e) s = {!!}
eval (case e1 e2 e3) s = {!!}


--eval (ƛ e) s = {!s!}
  
--eval : ∀ {Γ n} → Exp Γ n →  
