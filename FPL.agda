module FPL where

open import FAlg 
open import PL
open import Data.Nat
open import Data.Fin
open import Data.Unit
open import Data.Product
open import Data.Vec hiding ([_])

data EnvF : Alg → Set where
  val : {t : Alg} → ValG EnvF t → EnvF t 
  free : {u t : Alg} → EnvF (u ⊕ t)
  
fmapV : {t : Alg} {P Q : Alg → Set} → ({t' : Alg} → P t' → Q t') → ValG P t → ValG Q t
fmapV f V1 = V1
fmapV {t ⊗ u} f (a , b) = f a , f b
fmapV {t ⊕ u} f (inL a) = inL (f a)
fmapV {t ⊕ u} f (inR b) = inR (f b)

data PosV : Alg → Alg → Set where
   fst : ∀{t u} → PosV t (t ⊗ u) 
   snd : ∀{t u} → PosV u (t ⊗ u) 
   inL : ∀{t u} → PosV t (t ⊕ u) 
   inR : ∀{t u} → PosV u (t ⊕ u) 
   
fmapP : {t : Alg} {P Q : Alg → Set} → ((t' : Alg) → (PosV t' t) → P t' → Q t') → ValG P t → ValG Q t
fmapP f V1 = V1
fmapP {t ⊗ u} f (a , b) = f t fst a , f u snd b
fmapP {t ⊕ u} f (inL a) = inL (f t inL a)
fmapP {t ⊕ u} f (inR b) = inR (f u inR b)
   
data ValP {P : Alg → Set} : {t u : Alg} → (PosV t u) → P t → ValG P u → Set where
  fst : {t u : Alg}{a : P t}{b : P u} → ValP fst a ( a , b ) 
  snd : {t u : Alg}{a : P t}{b : P u} → ValP snd b ( a , b ) 
  inL : {t u : Alg}{a : P t} → ValP inL a (inL {u = u} a) 
  inR : {t u : Alg}{a : P u} → ValP inR a (inR {t = t} a) 
  --inR : 
  
fmapF : {t : Alg} {P Q : Alg → Set} → (b : ValG P t) →
           ({t' : Alg}{p : PosV t' t} → (a : P t') → (ValP p a b) → Q t') → 
             ValG Q t
fmapF V1 f = V1
fmapF (a , b) f = f a (fst {b = b}) , f b (snd {a = a})
fmapF (inL a) f = inL (f a inL) 
fmapF (inR b) f = inR (f b inR) 
   
data FVar : {t : Alg} → EnvF t → Alg → Set where
  here : {t : Alg} {x : EnvF t} → FVar x t
  there : {t u r : Alg}{a : EnvF t}{b : ValG EnvF u}{p : PosV t u} → 
                 ValP p a b → (x : FVar a r) → FVar (val b) r
--  infst : {t u r : Alg}{a : EnvF t}{b : EnvF u} → 
--             (x : FVar a r) → FVar (val (a , b)) r
--  insnd : {t u r : Alg}{a : EnvF t}{b : EnvF u} → 
--             (x : FVar b r) → FVar (val (a , b)) r
--  inL : {t u r : Alg} {a : EnvF t} → 
--             (x : FVar a r) → FVar {t ⊕ u} (val (inL a)) r
--  inR : {t u r : Alg} {a : EnvF u} → 
--             (x : FVar a r) → FVar {t ⊕ u} (val (inR a)) r

data ExpF {n : ℕ} {s : Alg} (Γ : Cxt n) (Δ : EnvF s) (t : Alg) : Set 

ValF : {n : ℕ} {t : Alg} (Γ : Cxt n) (Δ : EnvF t) → Alg → Set
ValF Γ Δ = ValG (ExpF Γ Δ) 
 
data ExpF {n}{s} Γ Δ t where
  val : (a : ValF Γ Δ t) → ExpF Γ Δ t 
  var : (v : Fin n) → (p : Γ [ v ]= t)  → ExpF Γ Δ t 
  varF : (x : FVar Δ t) → ExpF Γ Δ t 
  fst : {u : Alg} → ExpF Γ Δ (t ⊗ u) → ExpF Γ Δ t 
  snd : {u : Alg} → ExpF Γ Δ (u ⊗ t) → ExpF Γ Δ t
  case : {u v : Alg} → ExpF Γ Δ (u ⊕ v) → 
                  ExpF (u ∷ Γ) Δ t → ExpF (v ∷ Γ) Δ t → ExpF Γ Δ t

data _[_]:=_ : {t t' : Alg} (Δ : EnvF t) → FVar Δ t' → ValG (FVar Δ) t' → Set where
  here : ∀{t} (a : ValG EnvF t) → val a [ here ]:= fmapF a (λ a₁ x → there x here)
  there : ∀{t t'}{m : PosV t t'}{Δ : EnvF t}{Δ' : ValG EnvF t'}{p : FVar Δ t}{a : ValG (FVar Δ) t} → {p' : ValP m Δ Δ'} → 
                    Δ [ p ]:= a → val Δ' [ there p' p ]:= fmapF a (λ a₁ _ → there p' a₁)
  
  -- fmapF (λ a₁ x → varF (there {!!} here)) a 
  --here, : {u v : Alg} {a : EnvF u} {b : EnvF v} → 
  --    (a , b) [ here ]:= ( varF (infst here) , varF (insnd here) )
  --hereL : {u v : Alg} {a : EnvF u} → inL {u = v} a [ here ]:= inL (varF (inL here))
