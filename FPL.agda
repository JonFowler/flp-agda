module FPL where

open import FAlg 
open import PL
open import Subs
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product 
open import Data.Vec hiding ([_])
open import Data.Sum
open import Data.Unit
open import Relation.Nullary

data ExpF {n : ℕ}{γ : Alg} (s : EnvF γ) (Γ : Cxt n) (t : Alg) : Set where
   InE : ExpG (ExpF s) Γ t → ExpF s Γ t
   InF : VarF s t → ExpF s Γ t
   
ExpFVar : {γ : Alg} (s : EnvF γ) {n : ℕ} → Cxt n → ExpT 
ExpFVar s Γ Δ t = ExpF s (Δ ++ Γ) t 
   
foldVarF : ∀ {t γ m n o}{s : EnvF γ}{Γ : Cxt n}{Γ' : Cxt o}(Δ : Cxt m) → VarRule Γ Γ' (ExpFVar s) 
             →  ExpF s (Δ ++ Γ) t → ExpF s (Δ ++ Γ') t
foldVarF Δ f (InE (val V1)) = InE (val V1)
foldVarF Δ f (InE (val (a , b))) = InE (val (foldVarF Δ f a , foldVarF Δ f b))
foldVarF Δ f (InE (val (inL a))) = InE (val (inL (foldVarF Δ f a)))
foldVarF Δ f (InE (val (inR b))) = InE (val (inR (foldVarF Δ f b)))
foldVarF Δ f (InE (var x)) with f Δ x 
foldVarF Δ f (InE (var x)) | inj₁ e = e
foldVarF Δ f (InE (var x)) | inj₂ y = InE (var y)
foldVarF Δ f (InE (fst x)) = InE (fst (foldVarF Δ f x))
foldVarF Δ f (InE (snd x)) = InE (snd (foldVarF Δ f x))
foldVarF Δ f (InE (case {u = u} {v} x x₁ x₂)) = 
  InE (case (foldVarF Δ f x) (foldVarF (u ∷ Δ) f x₁) (foldVarF (v ∷ Δ) f x₂))
foldVarF Δ f (InF x) = InF x

foldVarF' : ∀ {t γ m n o}{s : EnvF γ}{Γ : Cxt n}{Γ' : Cxt o}(Δ : Cxt m) → VarRule' Γ Γ'  → 
        ExpF s (Δ ++ Γ) t → ExpF s (Δ ++ Γ') t
foldVarF' {s = s} Δ f = foldVarF Δ (VarRuleInj {P = ExpFVar s} f)

addEF : ∀{γ m n t}{s : EnvF γ}{Γ : Cxt n}  (Δ : Cxt m) (t' : Alg)  → 
     ExpF s (Δ ++ Γ) t → ExpF s (Δ ++ t' ∷ Γ) t
addEF Δ t = foldVarF' Δ addVar 

_∷EF_ : ∀{γ t n}{s : EnvF γ}{Γ : Cxt n} (t' : Alg) → ExpF s Γ t → ExpF s (t' ∷ Γ) t
_∷EF_ t = addEF [] t

ValF : {n : ℕ} {γ : Alg}(s : EnvF γ)(Γ : Cxt n)  → Alg → Set
ValF s Γ = ValG (ExpF s Γ) 

--data ExpF {n}{s} Γ Δ t where
--  val : (a : ValF Γ Δ t) → ExpF Γ Δ t 
--  var : (v : Fin n) → (p : Γ [ v ]= t)  → ExpF Γ Δ t 
--  varF : (x : VarF Δ t) → ExpF Γ Δ t 
--  fst : {u : Alg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
--  snd : {u : Alg} → ExpF Γ Δ (u ⊗ t) → ExpF Γ Δ t
--  case : {u v : Alg} → ExpF Γ Δ (u ⊕ v) → 
--                  ExpF (u ∷ Γ) Δ t → ExpF (v ∷ Γ) Δ t → ExpF Γ Δ t

embValF : {n : ℕ}{γ t : Alg}{Γ : Cxt n}{s s' : EnvF γ} →  s <= s' → ValF s Γ t → ValF s' Γ t

embExpF : {n : ℕ}{γ t : Alg}{Γ : Cxt n}{s s' : EnvF γ} →  s <= s' → ExpF s Γ t → ExpF s' Γ t
embExpF o (InE (val a)) = InE (val (embValF o a))
embExpF o (InE (var x)) = InE (var x)
embExpF o (InE (fst x)) = InE (fst (embExpF o x))
embExpF o (InE (snd x)) = InE (snd (embExpF o x))
embExpF o (InE (case x x₁ x₂)) = InE (case (embExpF o x) (embExpF o x₁) (embExpF o x₂)) 
embExpF o (InF x) = InF (embVarF o x) 

embValF o V1 = V1
embValF o (a , b) = embExpF o a , embExpF o b
embValF o (inL a) = inL (embExpF o a)
embValF o (inR b) = inR (embExpF o b)

S :  ({n' : ℕ}{γ : Alg} → EnvF γ → Cxt n' → Alg → Set) → 
         {n : ℕ} → Cxt n → Alg → Alg → Set
S P Γ γ t = Σ (EnvF γ) (λ s → P s Γ t)

const : ∀{a}{A B : Set a} → A → B → A
const a b = a

data _⇓*_ {t γ : Alg} : S ExpF [] γ t → S ValF [] γ t → Set where 
  ⇓weak : {s s' s'' : EnvF γ}{e : ExpF s [] t}{a : ValF s' [] t} → 
             (s , e) ⇓* (s' , a) → (o : s' <= s'') → (s , e) ⇓* (s'' , embValF o a)
  ⇓var : {s : EnvF γ}{x : VarF s t}{a : ValG (VarF s) t} → s [ x ]:= a → 
                        (s , InF x) ⇓* (s , (fmapV InF a))
  ⇓Fvar : {s : EnvF γ}{x : VarF s t} → ¬ (∃ (_[_]:=_ s x)) → (a : ValG (λ _ → Unit) t) →
                        (s , InF x) ⇓* (insert s x (fmapV (const free) a) , fmapP {!!} a) 
  ⇓val : {s : EnvF γ} {a : ValF s [] t} → (s , InE (val a)) ⇓* (s , a) 
--  ⇓fst : {s : EnvF γ} → {!!} ⇓* {!!} 
--  ⇓caseL : ∀{u v}{s s' s'' : EnvF γ  }{e : ExpF [] s (u ⊕ v)}
--   {f1 : ExpF (u ∷ []) s t}{f2 : ExpF (v ∷ []) s t} {e' : ExpF [] s' u}
--   {a : ValF [] s'' t} → (s , e) ⇓* (s' , inL e') → f1 ⟨ e' ⟩ ⇓ a → (? , case e f1 f2) ⇓* (? , a)

--    a <= a' →  val  <= val (a' , b')

  
  

--data Test {t : Alg} (E : Alg → Set) (P : E t → ValG E t → Set)
--  : (E t) → (ValG E t) → Set1 where

--data ∣_∣_↓_ {t γ : Alg}{E : Alg → Set}
--     (P : E t → ValG E t → Set) : EnvF γ × E t → EnvF γ × ValG E t → 
--     Set where
--    pure : { → P e a → ∣ P ∣ {!!} , {!!} ↓ ({!!} , {!!}) 

  --fmapF (λ a₁ x → varF (there {!!} here)) a 
  --here, : {u v : Alg} {a : EnvF u} {b : EnvF v} → 
  --    (a , b) [ here ]:= ( varF (infst here) , varF (insnd here) )
  --hereL : {u v : Alg} {a : EnvF u} → inL {u = v} a [ here ]:= inL (varF (inL here))
