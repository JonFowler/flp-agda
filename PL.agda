module PL where

open import FAlg
open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Vec hiding (_>>=_)
open import Data.Empty
open import Data.Product 
open import Data.Sum
open import Relation.Binary.PropositionalEquality hiding ([_])

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
            
MapVarE : ∀{m n o} → Cxt m → Alg → Cxt n → Cxt o  → Set
MapVarE Δ t Γ Γ' = Exp (Δ ++ Γ) t → Exp (Δ ++ Γ') t

MapVarV : ∀{m n o} → Cxt n → Alg → Cxt o → Cxt m → Set
MapVarV Δ t Γ Γ' = Val (Δ ++ Γ) t → Val (Δ ++ Γ') t

mapVarE : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule Γ Γ' → (Δ : Cxt m) → MapVarE Δ t Γ Γ' 

mapVarV : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule Γ Γ' → (Δ : Cxt m) → MapVarV Δ t Γ Γ'
   
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
     MapVarE Δ s (t ∷ t1 ∷ Γ) (t1 ∷ t ∷ Γ)
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
     MapVarE Δ s Γ (t ∷ Γ)
addE Δ t = mapVarE (VarRuleInj (addVar {t = t})) Δ

addV : {m n : ℕ} {s : Alg} {Γ : Cxt n}  (Δ : Cxt m) (t : Alg)  → 
     MapVarV Δ s Γ (t ∷ Γ) 
addV Δ t = mapVarV (VarRuleInj (addVar {t = t})) Δ

_∷E_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Exp Γ s → Exp (t ∷ Γ) s
_∷E_ = addE []

_∷V_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Val Γ s → Val (t ∷ Γ) s
_∷V_ = addV []

data EnvG (P : {m : ℕ} → Cxt m → Alg → Set) : {n : ℕ} → Cxt n → Set where
  [] : EnvG P []
  _∷_ : ∀ {t n} {Γ : Cxt n} → P Γ t → EnvG P Γ → EnvG P (t ∷ Γ)
  
Env : {n : ℕ} → Cxt n → Set
Env = EnvG Exp

embExpVar : ∀{n u t}{Γ : Cxt n} → Exp Γ t  ⊎  Σ (Fin n) (λ x →  Γ [ x ]= t) 
                              → Exp (u ∷ Γ) t  ⊎  Σ (Fin (suc n)) (λ x →  (u ∷ Γ) [ x ]= t)
embExpVar {u = u} (inj₁ x) = inj₁ (u ∷E x)
embExpVar (inj₂ y) = inj₂ (embVar y)


subsVar : ∀{n t}{Γ : Cxt n} → (e : Exp Γ t) → VarRule (t ∷ Γ) Γ
subsVar e [] zero here = inj₁ e
subsVar e [] (suc v) (there p) = inj₂ (v , p)
subsVar e (t' ∷ Δ) zero here = inj₂ (zero , here)
subsVar e (x ∷ Δ) (suc v) (there p) = embExpVar (subsVar e Δ v p)
  
subsE : ∀ {m n t u} {Γ : Cxt n} → (Δ : Cxt m) → Exp Γ t → MapVarE Δ u (t ∷ Γ) Γ  
subsE Δ e = mapVarE (subsVar e) Δ

_⟨_⟩ : ∀{n u t}{Γ : Cxt n} → Exp (u ∷ Γ) t → Exp Γ u → Exp Γ t
f ⟨ e ⟩ = subsE [] e f

data _⇓_ {t : Alg} : Exp [] t → Val [] t → Set where
  ⇓-val : {a : Val [] t} → val a ⇓ a
  ⇓-fst : ∀{u}{e : Exp [] (t ⊗ u)} {e1 : Exp [] t} {e2 : Exp [] u} {a : Val [] t} 
                         → e  ⇓ ( e1 , e2 ) → e1  ⇓ a → fst e  ⇓ a
  ⇓-snd : ∀{u}{e : Exp [] (u ⊗ t)} {e1 : Exp [] u} {e2 : Exp [] t} {a : Val [] t} 
                         → e  ⇓ ( e1 , e2 ) → e2  ⇓ a → snd e  ⇓ a
  ⇓-caseL : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t} {e' : Exp [] u}
   {a : Val [] t} → e ⇓ (inL e') → f1 ⟨ e' ⟩ ⇓ a → case e f1 f2 ⇓ a 
  ⇓-caseR : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t}{e' : Exp [] v}
   {a : Val [] t} → e ⇓ (inR e') → f2 ⟨ e' ⟩ ⇓ a → case e f1 f2 ⇓ a 


