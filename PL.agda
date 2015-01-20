module PL where

open import FAlg
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (_>>=_)
open import Data.Empty
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality

Cxt : ℕ → Set
Cxt n = Vec Alg n

--data _×_ : Set → Set → Set1 where
--  _,_ : ∀ {A B} → (a : A) → (b : B) → A × B


data Exp {n : ℕ} (Γ : Cxt n) (t : Alg) : Set

data Val {n : ℕ} (Γ : Cxt n) : Alg → Set where
  V1 : Val Γ K1
  _,_ : {t u : Alg} → (a : Exp Γ t) → (b : Exp Γ u) → Val Γ (t ⊗ u)
  inL : {t u : Alg} → (a : Exp Γ t) → Val Γ (t ⊕ u)
  inR : {t u : Alg} → (b : Exp Γ u) → Val Γ (t ⊕ u)
 
data Exp {n} Γ t where
  val : (a : Val Γ t) → Exp Γ t 
  var : (x : Fin n) → (p : Γ [ x ]= t) → Exp Γ t
  fst : {u : Alg} → Exp Γ (t ⊗ u) → Exp Γ t 
  snd : {u : Alg} → Exp Γ (u ⊗ t) → Exp Γ t
  case : {u v : Alg} → Exp Γ (u ⊕ v) → 
                          Exp (u ∷ Γ) t → Exp (v ∷ Γ) t → Exp Γ t
--  ƛ : {t u : FAlg} → Exp (t ∷ Γ) u → Exp Γ u

fstV : ∀ {n t u} {Γ : Cxt n} → Val Γ (t ⊗ u) → Exp Γ t
fstV (a , b) = a

sndV : ∀ {n t u} {Γ : Cxt n} → Val Γ (u ⊗ t) → Exp Γ t
sndV (a , b) = b

caseV : ∀ {n t u} {A : Set} {Γ : Cxt n} → Val Γ (t ⊕ u) → (Exp Γ t → A) → (Exp Γ u → A) → A
caseV (inL a) f g = f a
caseV (inR b) f g = g b

--ExpSub : {n : ℕ} {s : Alg} {Γ : Cxt n} (P : ∀ {m} → Cxt m → Σ ℕ Cxt)  → 
--      Exp Γ s →  
--      (∀ {m t} {Δ : Cxt m} → (i : Fin m) → ( Δ [ i ]= t ) → Exp (proj₂ (P Γ)) t )→ 
--      Exp (proj₂ (P Γ)) s
--ExpSub P (val a) f = {!!}
--ExpSub P (var x p) f = f x p
--ExpSub P (fst e) f = fst (ExpSub P e f)
--ExpSub P (snd e) f = snd (ExpSub P e f)
--ExpSub P (case e e₁ e₂) f = case (ExpSub P e f) (ExpSub P e₁ f) (ExpSub P e₂ f)

VarRule : ∀{n o}(Γ : Cxt n)(Γ' : Cxt o) → Set
VarRule {n}{o} Γ Γ' = ∀{t' m'} (Δ' : Cxt m') (x : Fin (m' + n)) → Δ' ++ Γ [ x ]= t' → 
            Exp (Δ' ++ Γ') t'  ⊎  
            Σ (Fin (m' + o)) (λ x' → Δ' ++ Γ' [ x' ]= t') 
            
VarRule' : ∀{n o}(Γ : Cxt n)(Γ' : Cxt o) → Set
VarRule' {n}{o} Γ Γ' = ∀{t' m'} (Δ' : Cxt m') (x : Fin (m' + n)) → Δ' ++ Γ [ x ]= t' → 
            Σ (Fin (m' + o)) (λ x' → Δ' ++ Γ' [ x' ]= t') 
            
VarRuleInj : ∀{n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule' Γ Γ' → VarRule Γ Γ'
VarRuleInj P Δ v p = inj₂ (P Δ v p)
            
MapVarE : ∀{m n o} → Alg → Cxt n → Cxt o → Cxt m → Set
MapVarE t Γ Γ' Δ = Exp (Δ ++ Γ) t → Exp (Δ ++ Γ') t

MapVarV : ∀{m n o} → Alg → Cxt n → Cxt o → Cxt m → Set
MapVarV t Γ Γ' Δ = Val (Δ ++ Γ) t → Val (Δ ++ Γ') t

mapVarE : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule Γ Γ' → (Δ : Cxt m) → MapVarE t Γ Γ' Δ

mapVarV : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule Γ Γ' → (Δ : Cxt m) → MapVarV t Γ Γ' Δ
   
mapVarE P Δ (val a) = val (mapVarV P Δ a)
mapVarE P Δ (var x p) with P Δ x p 
mapVarE P Δ (var x p) | inj₁ x₁ = x₁
mapVarE P Δ (var x p) | inj₂ (v' , p') = var v' p'
mapVarE P Δ (fst e) = fst (mapVarE P Δ e)
mapVarE P Δ (snd e) = snd (mapVarE P Δ e)
mapVarE P Δ (case {u = u}{v} e e₁ e₂) = case (mapVarE P Δ e) (mapVarE P (u ∷ Δ) e₁)
                               (mapVarE P (v ∷ Δ) e₂)

mapVarV P Δ V1 = V1
mapVarV P Δ (a , b) = mapVarE P Δ a , mapVarE P Δ b
mapVarV P Δ (inL a) = inL (mapVarE P Δ a)
mapVarV P Δ (inR b) = inR (mapVarE P Δ b)

swapVar : ∀{n t t'}{Γ : Cxt n} → VarRule' (t ∷ t' ∷ Γ) (t' ∷ t ∷ Γ)
swapVar [] zero here = (suc zero , there here)
swapVar [] (suc zero) (there here) = (zero , here)
swapVar [] (suc (suc v)) (there (there p)) = (suc (suc v) , there (there p))
swapVar (t'' ∷ Δ) zero here = (zero , here)
swapVar (x ∷ Δ) (suc v) (there p) with swapVar Δ v p
swapVar (x ∷ Δ) (suc v) (there p) | v' , p' = suc v' , there p'

swapE : {m n : ℕ} {s : Alg} {Γ : Cxt n} {t t1 : Alg} (Δ : Cxt m)  → 
     MapVarE s (t ∷ t1 ∷ Γ) (t1 ∷ t ∷ Γ) Δ  
swapE = mapVarE (VarRuleInj swapVar)

embVar : ∀ {u t n}{Γ : Cxt n} → Σ (Fin n)       (λ v → Γ       [ v ]= t) → 
                                 Σ (Fin (suc n)) (λ v → (u ∷ Γ) [ v ]= t)
embVar (v , p) = suc v , there p

addVar : ∀{n t}{Γ : Cxt n} → VarRule' Γ (t ∷ Γ)
addVar [] zero here = suc zero , there here
addVar [] (suc v) (there p) = embVar (addVar [] v p)
addVar (t' ∷ Δ) zero here = zero , here
addVar (x ∷ Δ) (suc v) (there p) = embVar (addVar Δ v p)

addE : {m n : ℕ} {s : Alg} {Γ : Cxt n}  (Δ : Cxt m) (t : Alg)  → 
     MapVarE s Γ (t ∷ Γ) Δ  
addE Δ t = mapVarE (VarRuleInj (addVar {t = t})) Δ

addV : {m n : ℕ} {s : Alg} {Γ : Cxt n}  (Δ : Cxt m) (t : Alg)  → 
     MapVarV s Γ (t ∷ Γ) Δ  
addV Δ t = mapVarV (VarRuleInj (addVar {t = t})) Δ

_∷E_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Exp Γ s → Exp (t ∷ Γ) s
_∷E_ = addE []

_∷V_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Val Γ s → Val (t ∷ Γ) s
_∷V_ = addV []

data EnvG (P : {m : ℕ} → Cxt m → Alg → Set) : {n : ℕ} → Cxt n → Set where
  [] : EnvG P []
  _∷_ : ∀ {t n} {Γ : Cxt n} → P Γ t → EnvG P Γ → EnvG P (t ∷ Γ)
  
--Env : {n : ℕ} → Cxt n → Set
--Env = EnvG Exp
--  
--emb : {n : ℕ} → Fin n → Fin (suc n)
--emb zero = zero
--emb (suc i) = suc (emb i)
--
--_C-_ : {n : ℕ}  → Cxt n → (i : Fin n) → Cxt (n ℕ-ℕ emb i)
--_C-_  Γ zero    = Γ 
--_C-_  (x ∷ Γ) (suc i) = Γ C- i
--
--_C1-_ : {n : ℕ}  → Cxt n → (i : Fin n) → Cxt (n ℕ-ℕ suc i)
--_C1-_  (x ∷ Γ) zero    = Γ 
--_C1-_  (x ∷ Γ) (suc i) = Γ C1- i 
--  
--lookupE : {n : ℕ}{Γ : Cxt n} → (i : Fin n) → Env Γ → Exp (Γ C1- i) (lookup i Γ) 
--lookupE zero (x ∷ s) = x 
--lookupE (suc i) (x ∷ s) = lookupE i s 
--
--State : Set → Set → Set
--State S A = S → (A × S)
--
--subsV : ∀ {m n t u} {Γ : Cxt n} → (Δ : Cxt m) → Val (Δ ++ t ∷ Γ) u → Exp Γ t → Val (Δ ++ Γ) u
--
--subsE : ∀ {m n t u} {Γ : Cxt n} → (Δ : Cxt m) → Exp (Δ ++ t ∷ Γ) u → Exp Γ t → Exp (Δ ++ Γ) u
--
--
--temp2 : ∀{m n} {Γ : Cxt n} {s : Alg} {t : Alg} → (Δ : Cxt m) → (x : Fin (m + (suc n))) → 
--                   (Δ ++ t ∷ Γ) [ x ]= s → Exp Γ t →
--       Σ (Fin (m + n)) (λ x1 → (Δ ++ Γ) [ x1 ]= s ) ⊎ Exp (Δ ++ Γ) s 
--temp2 [] zero here e = inj₂ e 
--temp2 [] (suc x) (there p) _ = inj₁ (x , p)
--temp2 (t ∷ Δ) zero here _ = inj₁ (zero , here)
--temp2 (t ∷ Δ) (suc x) (there p) e with temp2 Δ x p e
--temp2 (t ∷ Δ) (suc x) (there p) _ | inj₁ (x' , p') = inj₁ ((suc x') , (there p'))
--temp2 (t ∷ Δ) (suc x) (there p) _ | inj₂ e = inj₂ ( t ∷E e )
--
--subsE Δ (val a) e2 = val (subsV Δ a e2)
--subsE Δ (var x p) e2 with temp2 Δ x p e2
--subsE Δ (var x p) e2 | inj₁ (x' , p') = var x' p'
--subsE Δ (var x p) e2 | inj₂ e = e
--subsE Δ (fst e) e2 = fst (subsE Δ e e2)
--subsE Δ (snd e) e2 = snd (subsE Δ e e2)
--subsE Δ (case {t} {u} e e₁ e₂) e2 = case (subsE Δ e e2) (subsE (t ∷ Δ) e₁ e2) (subsE (u ∷ Δ) e₂ e2)
--
--subsV Δ V1 e = V1
--subsV Δ (a , b) e = (subsE Δ a e) , (subsE Δ b e)
--subsV Δ (inL a) e = inL (subsE Δ a e)
--subsV Δ (inR b) e = inR (subsE Δ b e)
--
--subsEnv : ∀ {n u} {Γ : Cxt n} → Exp Γ u → Env Γ → Exp [] u
--subsEnv e [] = e
--subsEnv e (x ∷ s) = subsEnv (subsE [] e x) s
--
--
--data _⇓_ {t : Alg} : {n : ℕ} {Γ : Cxt n} → Exp Γ t × Env Γ → Val Γ t → Set where
--  ⇓-val : {n : ℕ} {Γ : Cxt n}  {s : Env Γ} → {a : Val Γ t} → (val a , s) ⇓ a
--  ⇓-var0 : {n : ℕ} {Γ : Cxt n} {e : Exp Γ t} {s : Env Γ} {a : Val Γ t} → (e , s) ⇓ a  → (var zero here , e ∷ s) ⇓ (t ∷V a )
--  ⇓-var : ∀ {n t1}  {i : Fin n} {Γ : Cxt n} {e : Exp Γ t1} {s : Env Γ} {a : Val Γ t} {p : Γ [ i ]= t} → (var i p , s) ⇓ a  → (var (suc i) (there p) , e ∷ s) ⇓ (t1 ∷V a )
--  ⇓-fst : ∀ {u} {n : ℕ} {Γ : Cxt n} {s : Env Γ} {e : Exp Γ (t ⊗ u)} {e1 : Exp Γ t} {e2 : Exp Γ u} {a : Val Γ t} 
--                         → (e , s) ⇓ ( e1 , e2 ) → (e1 , s) ⇓ a → (fst e , s) ⇓ a
--  ⇓-snd : ∀ {u} {n : ℕ} {Γ : Cxt n}  {s : Env Γ} {e : Exp Γ (u ⊗ t)} {e1 : Exp Γ u} {e2 : Exp Γ t} {a : Val Γ t} 
--                         → (e , s) ⇓ ( e1 , e2 ) → (e2 , s) ⇓ a → (snd e , s) ⇓ a
--  ⇓-caseL : ∀ {u1 u2} {n : ℕ} {Γ : Cxt n}  {s : Env Γ} {e : Exp Γ (u1 ⊕ u2)} {e1 : Exp (u1 ∷ Γ) t } {e2 : Exp (u2 ∷ Γ) t} 
--                      {a : Exp Γ u1} {b : Val Γ t}
--                         → (e , s) ⇓ (inL a) → (subsE [] e1 a , s) ⇓ b → (case e e1 e2 , s) ⇓ b 
--  ⇓-caseR : ∀ {u1 u2} {n : ℕ} {Γ : Cxt n}  {s : Env Γ} {e : Exp Γ (u1 ⊕ u2)} {e1 : Exp (u1 ∷ Γ) t } {e2 : Exp (u2 ∷ Γ) t} 
--                      {a : Exp Γ u2} {b : Val Γ t}
--                         → (e , s) ⇓ (inR a) → (subsE [] e2 a , s) ⇓ b → (case e e1 e2 , s) ⇓ b 
--
--                         
--⇓-subNorm : ∀ {t n} {Γ : Cxt n} {a : Val Γ t} → (e : Exp Γ t) → (s : Env Γ) →  
--                 Σ (Val [] t) (λ x → (subsEnv e s , []) ⇓ x)
--⇓-subNorm {t ⊕ t₁} e s = {!e!}
--⇓-subNorm {K1} e s = {!e!}
--⇓-subNorm {t ⊗ t₁} e s = {!!}

--⇓-norm : ∀ {t } (e : Exp [] t) → Σ (Val [] t) (λ x → e ⇓ x)
--⇓-norm (val a) = a , ⇓-val
--⇓-norm (var () p)
--⇓-norm (fst e) = {!!} 
--⇓-norm (snd e) = {!!}
--⇓-norm (case e0 e1 e2) = {!!}




  
  
 
--eval : ∀ {t n} {Γ : Cxt n} → Exp Γ t  → Env Γ → Val Γ t
--eval (val a) s = a  
--eval {Γ = t ∷ Γ} (var zero here) (e ∷ s) = t ∷V eval e s 
--eval {Γ = t ∷ Γ} (var (suc x) (there p)) (e ∷ s) = t ∷V eval (var x p) s
--eval (fst e) s = {!eval (fstV (eval e s)) s!}
--eval (snd e) s = {!!}
--eval (case e1 e2 e3) s with eval e1 s 
--eval (case e1 e2 e3) s | inL a = {!eval (subsE [] e2 a) s!}
--eval (case e1 e2 e3) s | inR b = {!!}


--eval (ƛ e) s = {!s!}
  
--eval : ∀ {Γ n} → Exp Γ n →  
