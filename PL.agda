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

{-
EXPRESSION DEFINITION
-}

data ValG (P : Alg → Set) : Alg → Set where
  V1 : ValG P K1
  _,_ : {t u : Alg} → (a : P t) → (b : P u) → ValG P (t ⊗ u)
  inL : {t u : Alg} → (a : P t) → ValG P (t ⊕ u)
  inR : {t u : Alg} → (b : P u) → ValG P (t ⊕ u)
  
--data Exp {n : ℕ} (Γ : Cxt n) (t : Alg) : Set
 
--Val : {n : ℕ} → Cxt n → Alg → Set
--Val Γ t = ValG (Exp Γ) t

ExpT : {m : ℕ} → Cxt m → Set₁
ExpT Δ = {n : ℕ} → Cxt n → Alg → Set

data ExpG {n : ℕ}(Γ : Cxt n)(P : ExpT Γ){m : ℕ}(Δ : Cxt m)(t : Alg) : Set                  

data ExpG {n} Γ P {m} Δ t where
  val : (a : ValG (P Δ) t) → ExpG Γ P Δ t 
  var : (x : Fin (m + n)) → (p : (Δ ++ Γ) [ x ]= t) → ExpG Γ P Δ t
  fst : {u : Alg} → P Δ (t ⊗ u) → ExpG Γ P Δ t 
  snd : {u : Alg} → P Δ (u ⊗ t) → ExpG Γ P Δ t
  case : {u v : Alg} → P Δ (u ⊕ v) → 
            P (u ∷ Δ) t → P (v ∷ Δ) t → ExpG Γ P Δ t
--                          
data Exp' {n : ℕ} (Γ : Cxt n) {m : ℕ} (Δ : Cxt m) (t : Alg) : Set where
   In : ExpG Γ (Exp' Γ) Δ t → Exp' Γ Δ t

--data Exp {n} Γ t where
--  val : (a : Val Γ t) → Exp Γ t 
--  var : (x : Fin n) → (p : Γ [ x ]= t) → Exp Γ t
--  fst : {u : Alg} → Exp Γ (t ⊗ u) → Exp Γ t 
--  snd : {u : Alg} → Exp Γ (u ⊗ t) → Exp Γ t
--  case : {u v : Alg} → Exp Γ (u ⊕ v) → 
--                          Exp (u ∷ Γ) t → Exp (v ∷ Γ) t → Exp Γ t

ExpFold : {n : ℕ}(Γ : Cxt n) → ExpT Γ → Set
ExpFold Γ A = {t : Alg}{m : ℕ}(Δ : Cxt m) → ExpG Γ A Δ t → A Δ t

fmapExp : {n : ℕ}{Γ : Cxt n}{A B : ExpT Γ} → 
      ({m' : ℕ}{t : Alg} → (Δ' : Cxt m') → A Δ' t       → B Δ' t) → 
       {m : ℕ} {t : Alg} → (Δ  : Cxt m ) → ExpG Γ A Δ t → ExpG Γ B Δ t
fmapExp f Δ (val V1) = val V1
fmapExp f Δ (val (a , b)) = val (f Δ a , f Δ b)
fmapExp f Δ (val (inL a)) = val (inL (f Δ a))
fmapExp f Δ (val (inR b)) = val (inR (f Δ b))
fmapExp f Δ (var x p) = var x p
fmapExp f Δ (fst x) = fst (f Δ x)
fmapExp f Δ (snd x) = snd (f Δ x)
fmapExp f Δ (case {u = u}{v} x x₁ x₂) = case (f Δ x) (f (u ∷ Δ) x₁) (f (v ∷ Δ) x₂)

---- Nice version of foldExp doesn't work due to termination checker
foldExp : {n : ℕ}{Γ : Cxt n}{A : ExpT Γ} → ExpFold Γ A → 
    {t : Alg}{m : ℕ} → (Δ : Cxt m) → Exp' Γ Δ t → A Δ t
foldExp f Δ (In (val V1)) = f Δ (val V1)
foldExp f Δ (In (val (a , b))) =  f Δ (val (foldExp f Δ a , foldExp f Δ b))
foldExp f Δ (In (val (inL a))) =  f Δ (val (inL (foldExp f Δ a)))
foldExp f Δ (In (val (inR b))) =  f Δ (val (inR (foldExp f Δ b)))
foldExp f Δ (In (var x p)) = f Δ (var x p) -- f Δ (var x p)
foldExp f Δ (In (fst x)) = f Δ (fst (foldExp f Δ x))
foldExp f Δ (In (snd x)) = f Δ (snd (foldExp f Δ x))
foldExp f Δ (In (case {u = u}{v} x x₁ x₂)) = 
      f Δ (case (foldExp f Δ x) (foldExp f (u ∷ Δ) x₁) (foldExp f (v ∷ Δ) x₂))

fstV : ∀ {t u}{P : Alg → Set} → ValG P (t ⊗ u) → P t
fstV (a , b) = a

sndV : ∀ {t u}{P : Alg → Set} → ValG P (u ⊗ t) → P t
sndV (a , b) = b

caseV : ∀ {t u} {A : Set}{P : Alg → Set} → ValG P (t ⊕ u) → (P t → A) → (P u → A) → A
caseV (inL a) f g = f a
caseV (inR b) f g = g b


----SUBSTITUITION RULES

VarRule : ∀{n o}(Γ : Cxt n)(P : ExpT Γ)(Γ' : Cxt o) → Set
VarRule {n}{o} Γ P Γ' = ∀{t m} (Δ : Cxt m) (x : Fin (m + n)) → Δ ++ Γ [ x ]= t → 
            ExpG Γ' P Δ t  ⊎  
            Σ (Fin (m + o)) (λ x' → Δ ++ Γ' [ x' ]= t) 
            
VarRule' : ∀{n o}(Γ : Cxt n)(Γ' : Cxt o) → Set
VarRule' {n}{o} Γ Γ' = ∀{t' m'} (Δ' : Cxt m') (x : Fin (m' + n)) → Δ' ++ Γ [ x ]= t' → 
            Σ (Fin (m' + o)) (λ x' → Δ' ++ Γ' [ x' ]= t') 
            
VarRuleInj : ∀{n o}{Γ : Cxt n}(P : ExpT Γ){Γ' : Cxt o} → VarRule' Γ Γ' → VarRule Γ P Γ'
VarRuleInj P f Δ v p = inj₂ (f Δ v p)
            
--MapVarE : ∀{m n o}(P : ExpT) → Cxt m → Alg → Cxt n → Cxt o  → Set
--MapVarE P Δ t Γ Γ' = ExpG P (Δ ++ Γ) t → ExpG P (Δ ++ Γ') t
--
--MapVar : (A :  → VarRule P Γ Γ' → ExpFold ( )
--
--MapVarV : ∀{m n o} → Cxt n → Alg → Cxt o → Cxt m → Set
--MapVarV Δ t Γ Γ' = Val (Δ ++ Γ) t → Val (Δ ++ Γ') t
--
--mapVarE : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o}{P : ExpT} → VarRule P Γ Γ' → 
--  (Δ : Cxt m) → MapVarE P Δ t Γ Γ' 

--mapVarV : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o} → VarRule P Γ Γ' → (Δ : Cxt m) → MapVarV P Δ t Γ Γ'
----   
--mapVarE P Δ (val a) = ? 
--mapVarE P Δ (var x p) with P Δ x p 
--mapVarE P Δ (var x p) | inj₁ x₁ = x₁
--mapVarE P Δ (var x p) | inj₂ (v' , p') = var v' p'
--mapVarE P Δ (fst e) = fst e   --(mapVarE P Δ e)
--mapVarE P Δ (snd e) = snd e   --(mapVarE P Δ e)
--mapVarE P Δ (case {u = u}{v} e e₁ e₂) = case (mapVarE P Δ e) (mapVarE P (u ∷ Δ) e₁)
--                               (mapVarE P (v ∷ Δ) e₂)
----
--mapVarV P Δ V1 = V1
--mapVarV P Δ (a , b) = mapVarE P Δ a , mapVarE P Δ b
--mapVarV P Δ (inL a) = inL (mapVarE P Δ a)
--mapVarV P Δ (inR b) = inR (mapVarE P Δ b)
--
--swapVar : ∀{n t t'}{Γ : Cxt n} → VarRule' (t ∷ t' ∷ Γ) (t' ∷ t ∷ Γ)
--swapVar [] zero here = (suc zero , there here)
--swapVar [] (suc zero) (there here) = (zero , here)
--swapVar [] (suc (suc v)) (there (there p)) = (suc (suc v) , there (there p))
--swapVar (t'' ∷ Δ) zero here = (zero , here)
--swapVar (x ∷ Δ) (suc v) (there p) with swapVar Δ v p
--swapVar (x ∷ Δ) (suc v) (there p) | v' , p' = suc v' , there p'
--
--swapE : {m n : ℕ} {s : Alg} {Γ : Cxt n} {t t1 : Alg} (Δ : Cxt m)  → 
--     MapVarE Δ s (t ∷ t1 ∷ Γ) (t1 ∷ t ∷ Γ)
--swapE = mapVarE (VarRuleInj swapVar)
--
--embVar : ∀ {u t n}{Γ : Cxt n} → Σ (Fin n)       (λ v → Γ       [ v ]= t) → 
--                                 Σ (Fin (suc n)) (λ v → (u ∷ Γ) [ v ]= t)
--embVar (v , p) = suc v , there p
--
--addVar : ∀{n t}{Γ : Cxt n} → VarRule' Γ (t ∷ Γ)
--addVar [] zero here = suc zero , there here
--addVar [] (suc v) (there p) = embVar (addVar [] v p)
--addVar (t' ∷ Δ) zero here = zero , here
--addVar (x ∷ Δ) (suc v) (there p) = embVar (addVar Δ v p)
--
--addE : {m n : ℕ} {s : Alg} {Γ : Cxt n}  (Δ : Cxt m) (t : Alg)  → 
--     MapVarE Δ s Γ (t ∷ Γ)
--addE Δ t = mapVarE (VarRuleInj (addVar {t = t})) Δ
--
--addV : {m n : ℕ} {s : Alg} {Γ : Cxt n}  (Δ : Cxt m) (t : Alg)  → 
--     MapVarV Δ s Γ (t ∷ Γ) 
--addV Δ t = mapVarV (VarRuleInj (addVar {t = t})) Δ
--
--_∷E_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Exp Γ s → Exp (t ∷ Γ) s
--_∷E_ = addE []
--
--_∷V_ : {n : ℕ} {s : Alg} {Γ : Cxt n} → (t : Alg) → Val Γ s → Val (t ∷ Γ) s
--_∷V_ = addV []
--

----ENVIRONMENT (UNUSED)

--
--data EnvG (P : {m : ℕ} → Cxt m → Alg → Set) : {n : ℕ} → Cxt n → Set where
--  [] : EnvG P []
--  _∷_ : ∀ {t n} {Γ : Cxt n} → P Γ t → EnvG P Γ → EnvG P (t ∷ Γ)
--  
--Env : {n : ℕ} → Cxt n → Set
--Env = EnvG Exp
--
--embExpVar : ∀{n u t}{Γ : Cxt n} → Exp Γ t  ⊎  Σ (Fin n) (λ x →  Γ [ x ]= t) 
--                              → Exp (u ∷ Γ) t  ⊎  Σ (Fin (suc n)) (λ x →  (u ∷ Γ) [ x ]= t)
--embExpVar {u = u} (inj₁ x) = inj₁ (u ∷E x)
--embExpVar (inj₂ y) = inj₂ (embVar y)
--
--subsVar : ∀{n t}{Γ : Cxt n} → (e : Exp Γ t) → VarRule (t ∷ Γ) Γ
--subsVar e [] zero here = inj₁ e
--subsVar e [] (suc v) (there p) = inj₂ (v , p)
--subsVar e (t' ∷ Δ) zero here = inj₂ (zero , here)
--subsVar e (x ∷ Δ) (suc v) (there p) = embExpVar (subsVar e Δ v p)
--  
--subsE : ∀ {m n t u} {Γ : Cxt n} → (Δ : Cxt m) → Exp Γ t → MapVarE Δ u (t ∷ Γ) Γ  
--subsE Δ e = mapVarE (subsVar e) Δ
--
--_⟨_⟩ : ∀{n u t}{Γ : Cxt n} → Exp (u ∷ Γ) t → Exp Γ u → Exp Γ t
--f ⟨ e ⟩ = subsE [] e f
--

----EVALUATION

--
--data _⇓_ {t : Alg} : Exp [] t → Val [] t → Set where
--  ⇓val : {a : Val [] t} → val a ⇓ a
--  ⇓fst : ∀{u}{e : Exp [] (t ⊗ u)} {e1 : Exp [] t} {e2 : Exp [] u} {a : Val [] t} 
--                         → e  ⇓ ( e1 , e2 ) → e1  ⇓ a → fst e  ⇓ a
--  ⇓snd : ∀{u}{e : Exp [] (u ⊗ t)} {e1 : Exp [] u} {e2 : Exp [] t} {a : Val [] t} 
--                         → e  ⇓ ( e1 , e2 ) → e2  ⇓ a → snd e  ⇓ a
--  ⇓caseL : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t} {e' : Exp [] u}
--   {a : Val [] t} → e ⇓ (inL e') → f1 ⟨ e' ⟩ ⇓ a → case e f1 f2 ⇓ a 
--  ⇓caseR : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t}{e' : Exp [] v}
--   {a : Val [] t} → e ⇓ (inR e') → f2 ⟨ e' ⟩ ⇓ a → case e f1 f2 ⇓ a 


