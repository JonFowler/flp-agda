module Subs where

open import FAlg 
open import PL
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product 
open import Data.Vec hiding ([_])

data EnvF : Alg → Set where
  val : {t : Alg} → ValG EnvF t → EnvF t 
  free : {t : Alg} → EnvF t
  
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
   
data VarF : {t : Alg} → EnvF t → Alg → Set where
  here : {t : Alg} {x : EnvF t} → VarF x t
  there : {t u r : Alg}{a : EnvF t}{b : ValG EnvF u}{p : PosV t u} → 
                 ValP p a b → (x : VarF a r) → VarF (val b) r

data _[_]:=_ : {t t' : Alg} (Δ : EnvF t) → VarF Δ t' → ValG (VarF Δ) t' → Set where
  here : ∀{t} (a : ValG EnvF t) → val a [ here ]:= fmapF a (λ a₁ x → there x here)
  there : ∀{t t'}{m : PosV t t'}{Δ : EnvF t}{Δ' : ValG EnvF t'}{p : VarF Δ t}{a : ValG (VarF Δ) t} → {p' : ValP m Δ Δ'} → 
                    Δ [ p ]:= a → val Δ' [ there p' p ]:= fmapF a (λ a₁ _ → there p' a₁)
                    
onF : {t t' : Alg} {P : Alg → Set}{a : P t'}(b : ValG P t) → 
  {p : PosV t' t} → ValP p a b → (P t' → P t')  →  ValG P t
onF V1 () f
onF (a , b) fst f = f a , b
onF (a , b) snd f = a , f b
onF (inL a) inL f = inL (f a)
onF (inR b) inR f = inR (f b)

insert : {γ t : Alg} (Δ : EnvF γ) → VarF Δ t → ValG EnvF t → Σ (EnvF γ) (λ s → ValG (VarF s) t)
insert (val s) here a = val a , fmapF a (λ _ x → there x here)
insert (val s') (there {a = s} x p) a with insert s p a 
insert (val s') (there {p = pos} x p) a | proj₁ , proj₂ = 
  val (onF s' x (λ _ → proj₁)) , fmapF proj₂ (λ a₁ x₁ → there {!!} a₁)
insert free x a = {!!}
--insert (val x) here a = val a
--insert (val x) (there {a = a} x₁ x₂) a₁ 
--  = val (onF x x₁ (λ z → insert a x₂ a₁))
--insert free here a = val a

data _<=_ : {γ : Alg} → EnvF γ → EnvF γ → Set where
  ref : {γ : Alg} {a : EnvF γ} → a <= a 
  free : {γ : Alg} {a : EnvF γ} → free <= a 
  pair : {γ δ : Alg} {a a' : EnvF γ}{b b' : EnvF δ} → 
    a <= a' → b <= b' → val (a , b) <= val (a' , b')
  inL :  {γ δ : Alg} {a a'  : EnvF γ} → a <= a' → val (inL {u = δ} a) <= val (inL a')
  inR :  {γ δ : Alg} {a a'  : EnvF γ} → a <= a' → val (inR {t = δ} a) <= val (inR a')
  
embVarF : {γ t : Alg} {s s' : EnvF γ} → s <= s' → VarF s t →  VarF s' t
embVarF o here          = here
embVarF ref (there fst v)  = there fst v
embVarF (pair o _) (there fst v)  = there fst (embVarF o v)
embVarF ref (there snd v) = there snd v
embVarF (pair _ o₁)(there snd v) = there snd (embVarF o₁ v)
embVarF ref (there inL v) = there inL v
embVarF (inL o) (there inL v) = there inL (embVarF o v) 
embVarF ref (there inR v)  = there inR v
embVarF (inR o) (there inR v) = there inR (embVarF o v) 

