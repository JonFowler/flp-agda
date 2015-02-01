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
 
ExpT : Set₁
ExpT = {m : ℕ} → Cxt m → Alg → Set

data ExpG (P : ExpT){n : ℕ}(Γ : Cxt n)(t : Alg) : Set                  

Var : {n : ℕ} → (Cxt n) → (t : Alg) → Set
Var {n} Γ t =  Σ (Fin n) (λ x → Γ [ x ]= t)

data ExpG P {n} Γ t where
  val : (a : ValG (P Γ) t) → ExpG P Γ t 
  var : Var Γ t → ExpG P Γ t
  fst : {u : Alg} → P Γ (t ⊗ u) → ExpG P Γ t 
  snd : {u : Alg} → P Γ (u ⊗ t) → ExpG P Γ t
  case : {u v : Alg} → P Γ (u ⊕ v) → 
            P (u ∷ Γ) t → P (v ∷ Γ) t → ExpG P Γ t
--                          
data Exp {n : ℕ} (Γ : Cxt n) (t : Alg) : Set where
   In : ExpG Exp Γ t → Exp Γ  t
   
Val : {n : ℕ} → Cxt n → Alg → Set
Val Γ t = ValG (Exp Γ) t

--data Exp {n} Γ t where
--  val : (a : Val Γ t) → Exp Γ t 
--  var : (x : Fin n) → (p : Γ [ x ]= t) → Exp Γ t
--  fst : {u : Alg} → Exp Γ (t ⊗ u) → Exp Γ t 
--  snd : {u : Alg} → Exp Γ (u ⊗ t) → Exp Γ t
--  case : {u v : Alg} → Exp Γ (u ⊕ v) → 
--                          Exp (u ∷ Γ) t → Exp (v ∷ Γ) t → Exp Γ t

--ExpFold : {n : ℕ}(Γ : Cxt n) → ExpT → Set
--ExpFold Γ A = {t : Alg}{m : ℕ}(Δ : Cxt m) → ExpG Γ A Δ t → A Δ t
--
--fmapExp : {n : ℕ}{Γ : Cxt n}{A B : ExpT} → 
--      ({m' : ℕ}{t : Alg} → (Δ' : Cxt m') → A Δ' t → B Δ' t) → 
--       {m : ℕ} {t : Alg} → (Δ  : Cxt m ) → ExpG Γ A Δ t → ExpG Γ B Δ t
--fmapExp f Δ (val V1) = val V1
--fmapExp f Δ (val (a , b)) = val (f Δ a , f Δ b)
--fmapExp f Δ (val (inL a)) = val (inL (f Δ a))
--fmapExp f Δ (val (inR b)) = val (inR (f Δ b))
--fmapExp f Δ (var x) = var x
--fmapExp f Δ (fst x) = fst (f Δ x)
--fmapExp f Δ (snd x) = snd (f Δ x)
--fmapExp f Δ (case {u = u}{v} x x₁ x₂) = case (f Δ x) (f (u ∷ Δ) x₁) (f (v ∷ Δ) x₂)
--
------ Nice version of foldExp doesn't work due to termination checker
--foldExp : {n : ℕ}{Γ : Cxt n}{A : ExpT} → ExpFold Γ A → 
--    {t : Alg}{m : ℕ} → (Δ : Cxt m) → Exp Γ Δ t → A Δ t
--foldExp f Δ (In (val V1)) = f Δ (val V1)
--foldExp f Δ (In (val (a , b))) =  f Δ (val (foldExp f Δ a , foldExp f Δ b))
--foldExp f Δ (In (val (inL a))) =  f Δ (val (inL (foldExp f Δ a)))
--foldExp f Δ (In (val (inR b))) =  f Δ (val (inR (foldExp f Δ b)))
--foldExp f Δ (In (var x)) = f Δ (var x) -- f Δ (var x p)
--foldExp f Δ (In (fst x)) = f Δ (fst (foldExp f Δ x))
--foldExp f Δ (In (snd x)) = f Δ (snd (foldExp f Δ x))
--foldExp f Δ (In (case {u = u}{v} x x₁ x₂)) = 
--      f Δ (case (foldExp f Δ x) (foldExp f (u ∷ Δ) x₁) (foldExp f (v ∷ Δ) x₂))

fstV : ∀ {t u}{P : Alg → Set} → ValG P (t ⊗ u) → P t
fstV (a , b) = a

sndV : ∀ {t u}{P : Alg → Set} → ValG P (u ⊗ t) → P t
sndV (a , b) = b

caseV : ∀ {t u} {A : Set}{P : Alg → Set} → ValG P (t ⊕ u) → (P t → A) → (P u → A) → A
caseV (inL a) f g = f a
caseV (inR b) f g = g b 

----SUBSTITUITION RULES

VarRule : ∀{n o}(Γ : Cxt n)(Γ' : Cxt o)(P : Cxt o → ExpT) → Set
VarRule {n}{o} Γ Γ' P = ∀{t m} (Δ : Cxt m) → (Var (Δ ++ Γ) t) → 
            P Γ' Δ t  ⊎ Var (Δ ++ Γ') t
            --Σ (Fin (m + o)) (λ x' → Δ ++ Γ' [ x' ]= t) 
            
VarRule' : ∀{n o}(Γ : Cxt n)(Γ' : Cxt o) → Set
VarRule' {n}{o} Γ Γ' = ∀{t m} (Δ : Cxt m) → Var (Δ ++ Γ) t → 
           Var (Δ ++ Γ') t 
            
VarRuleInj : ∀{n o}{Γ : Cxt n}{Γ' : Cxt o}{P : Cxt o → ExpT} → VarRule' Γ Γ' → VarRule Γ Γ' P
VarRuleInj f Δ x = inj₂ (f Δ x)
            
MapVar : ∀{m n o} → Cxt m → (Γ : Cxt n) → (Γ' : Cxt o)  → 
        (P : ExpT) →  Alg →  Set
MapVar Δ Γ Γ' P t = ExpG P (Δ ++ Γ) t → ExpG P (Δ ++ Γ') t

ExpVar : {n : ℕ} → Cxt n → ExpT 
ExpVar Γ Δ t = Exp (Δ ++ Γ) t 

foldVar : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o}(Δ : Cxt m) → VarRule Γ Γ' ExpVar → 
        Exp (Δ ++ Γ) t → Exp (Δ ++ Γ') t
foldVar Δ f (In (val V1)) = In (val V1)
foldVar Δ f (In (val (a , b))) = In (val (foldVar Δ f a , foldVar Δ f b))
foldVar Δ f (In (val (inL a))) = In (val (inL (foldVar Δ f a)))
foldVar Δ f (In (val (inR b))) = In (val (inR (foldVar Δ f b)))
foldVar Δ f (In (var x)) with f Δ x 
foldVar Δ f (In (var x)) | inj₁ e = e 
foldVar Δ f (In (var x)) | inj₂ x' = In (var x')
foldVar Δ f (In (fst x)) = In (fst (foldVar Δ f x))
foldVar Δ f (In (snd x)) = In (snd (foldVar Δ f x))
foldVar Δ f (In (case {u = u}{v} x x₁ x₂)) = In (case (foldVar Δ f x) (foldVar (u ∷ Δ) f x₁) (foldVar (v ∷ Δ) f x₂)) 

foldVar' : ∀ {t m n o}{Γ : Cxt n}{Γ' : Cxt o}(Δ : Cxt m) → VarRule' Γ Γ'  → 
        Exp (Δ ++ Γ) t → Exp (Δ ++ Γ') t
foldVar' Δ f = foldVar Δ (VarRuleInj {P = ExpVar} f)

swapVar : ∀{n t t'}{Γ : Cxt n} → VarRule' (t ∷ t' ∷ Γ) (t' ∷ t ∷ Γ)
swapVar [] (zero , here) = (suc zero , there here)
swapVar [] ((suc zero) , (there here)) = (zero , here)
swapVar [] ((suc (suc v)) , (there (there p))) = (suc (suc v) , there (there p))
swapVar (t'' ∷ Δ) (zero , here) = (zero , here)
swapVar (x ∷ Δ) ((suc v) , (there p)) with swapVar Δ (v , p) 
swapVar (x ∷ Δ) ((suc v) , (there p)) | v' , p' = suc v' , there p'

swapE : ∀{m n t t'}{Γ : Cxt n}(Δ : Cxt m) →  Exp (Δ ++ t ∷ t' ∷ Γ) t → Exp (Δ ++ t' ∷ t ∷ Γ) t
swapE Δ = foldVar' Δ swapVar

embVar : ∀ {u t n}{Γ : Cxt n} → Var Γ t → Var (u ∷ Γ) t
embVar (v , p) = suc v , there p

addVar : ∀{n t}{Γ : Cxt n} → VarRule' Γ (t ∷ Γ)
addVar [] (zero , here) = suc zero , there here
addVar [] (suc x , there p) = embVar (addVar [] (x , p))
addVar (t ∷ Γ) (zero , here) = zero , here
addVar (t ∷ Γ) (suc x , there p) = embVar (addVar Γ (x , p))

addE : ∀{m n t} {Γ : Cxt n}  (Δ : Cxt m) (t' : Alg)  → Exp (Δ ++ Γ) t → Exp (Δ ++ t' ∷ Γ) t
addE Δ t = foldVar' Δ addVar 

_∷E_ : ∀{t n} {Γ : Cxt n} (t' : Alg) → Exp Γ t → Exp (t' ∷ Γ) t
_∷E_ t = addE [] t
--
--
----embExpVar : ∀{n u t}{Γ : Cxt n} → Exp Γ t  ⊎  Σ (Fin n) (λ x →  Γ [ x ]= t) 
----                              → Exp (u ∷ Γ) t  ⊎  Σ (Fin (suc n)) (λ x →  (u ∷ Γ) [ x ]= t)
----embExpVar {u = u} (inj₁ x) = inj₁ (u ∷E x)
----embExpVar (inj₂ y) = inj₂ (embVar y)

subsVar : ∀{n t}{Γ : Cxt n} → (e : Exp Γ t) → VarRule (t ∷ Γ) Γ ExpVar
subsVar e [] (zero , here) = inj₁ e
subsVar e [] (suc v , there p) = inj₂ (v , p)
subsVar e (t' ∷ Δ) (zero , here) = inj₂ (zero , here)
subsVar e (t ∷ Δ) (suc v , there p) with subsVar e Δ (v , p)
subsVar e (t ∷ Δ) (suc v , there p) | inj₁ e' = inj₁ (t ∷E e')
subsVar e (t ∷ Δ) (suc v , there p) | inj₂ x' = inj₂ (embVar x') --embExpVar (subsVar e Δ v p)
  
subsE : ∀ {m n t t'} {Γ : Cxt n} → (Δ : Cxt m) → Exp Γ t → Exp (Δ ++ t ∷ Γ) t' → 
                                                               Exp (Δ ++ Γ) t'
subsE Δ e = foldVar Δ (subsVar e) 

_⟨_⟩ : ∀{n u t}{Γ : Cxt n} → Exp (u ∷ Γ) t → Exp Γ u → Exp Γ t
f ⟨ e ⟩ = subsE [] e f


--EVALUATION


data _⇓_ {t : Alg} : Exp [] t → Val [] t → Set where
  ⇓val : {a : Val [] t} → In (val a) ⇓ a
  ⇓fst : ∀{u}{e : Exp [] (t ⊗ u)} {e1 : Exp [] t} {e2 : Exp [] u} {a : Val [] t} 
                         → e  ⇓ ( e1 , e2 ) → e1  ⇓ a → In (fst e)  ⇓ a
  ⇓snd : ∀{u}{e : Exp [] (u ⊗ t)} {e1 : Exp [] u} {e2 : Exp [] t} {a : Val [] t} 
                         → e  ⇓ ( e1 , e2 ) → e2  ⇓ a → In (snd e)  ⇓ a
  ⇓caseL : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t} {e' : Exp [] u}
   {a : Val [] t} → e ⇓ (inL e') → f1 ⟨ e' ⟩ ⇓ a → In (case e f1 f2) ⇓ a 
  ⇓caseR : ∀{u v}{e : Exp [] (u ⊕ v)}{f1 : Exp [ u ] t}{f2 : Exp [ v ] t}{e' : Exp [] v}
   {a : Val [] t} → e ⇓ (inR e') → f2 ⟨ e' ⟩ ⇓ a → In (case e f1 f2) ⇓ a 


