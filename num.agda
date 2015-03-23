module num where

open import Data.Product
open import Data.Vec
open import Data.Maybe as M
open import Data.Fin hiding (_+_ ) hiding (lift)
open import Data.Nat 
open import Function
open import Relation.Binary.PropositionalEquality


data Nat (A : Set) : Set where
  Z : Nat A
  S : A → Nat A
  
mapNat : {A B : Set} → (A → B) → Nat A → Nat B
mapNat f Z = Z
mapNat f (S x) =  S (f x) 
  
data NatSub : Set where
  hole : NatSub
  Z : NatSub
  S : NatSub → NatSub
  
  
data NatVar : NatSub → Set where
  here : {s : NatSub} → NatVar s
  there : {s : NatSub} → (p : NatVar s) → NatVar (S s)
  
updZ : (s : NatSub) → NatVar s → NatSub
updZ s here = Z 
updZ (S n) (there p) = S (updZ n p)

updS : (s : NatSub) → NatVar s → Σ NatSub NatVar
updS s here = S hole , there here
updS (S n) (there p) with updS n p
updS (S n) (there p) | s' , p' = S s' , there p'

repI : ∀{n}{A : Set} → (x : Fin n) → A →  Vec A n → Vec A n
repI zero a (x ∷ v) = a ∷ v
repI (suc n) a (x ∷ v) = x ∷ repI n a v
  
data _[_]:=_ : (s : NatSub) → (NatVar s) → Maybe (Nat (NatVar s)) → Set where 
  hereZ : Z [ here ]:= just Z 
  hereS : {a : NatSub} → S a [ here ]:= just (S (there here)) 
  there : {s : NatSub}{p : NatVar s}{n : Maybe (Nat (NatVar s))} → 
          s [ p ]:=  n → S s [ there p ]:= M.map (mapNat there) n
  
Subs : ℕ → Set
Subs = Vec NatSub 
  
data Exp {m : ℕ} (V : ℕ) (M : Subs m)  : Set where
  nat : Nat (Exp V M) → Exp V M
  var : Fin V → Exp V M
  mvar : (x : Fin m) → (p : NatVar (lookup x M) )  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : {V' m : ℕ}{M : Subs m}(V : ℕ) → Exp (V + V') M → Exp (V + suc V') M
sucExp V (nat Z) = nat Z
sucExp V (nat (S x)) = nat (S (sucExp V x))
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x p) = mvar x p
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

sub : {V' m : ℕ}{M : Subs m} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
sub V (nat Z) ef = nat Z
sub V (nat (S x)) ef = nat (S (sub V x ef))
sub zero (var zero) ef = ef
sub zero (var (suc x)) ef = var x
sub (suc V) (var zero) ef = var zero
sub (suc V) (var (suc x)) ef with sub V (var x) ef
... | e' = sucExp 0 e'
sub V (mvar x p) ef = mvar x p
sub V (case e alt₀ e₁ altₛ e₂) ef = case sub V e ef alt₀ sub V e₁ ef altₛ sub (suc V) e₂ ef
  
_[-_-] : {V m : ℕ}{M : Subs m} → Exp (suc V) M → Exp V M → Exp V M
_[-_-] = sub 0
  
data _↦R_ {m : ℕ}{M : Subs m} : Exp 0 M → Exp 0 M → Set where
  caseZ :  (e : Exp 0 M) → (e' : Exp 1 M) → case (nat Z) alt₀ e altₛ e' ↦R e
  caseS : {ef : Exp 0 M} → (e : Exp 0 M) → (e' : Exp 1 M)   
                → case (nat (S ef)) alt₀ e altₛ e' ↦R e' [- ef -]

data Cxt {m : ℕ} (V : ℕ) (M : Subs m)  : Set where
  hole : Cxt V M
  case_alt₀_altₛ_ : Cxt V M → Exp V M → Exp (suc V) M → Cxt V M
  
  
_[/_] : ∀{m V}{M : Subs m} → Cxt V M → Exp V M → Exp V M
hole [/ e ] = e
(case H alt₀ x altₛ x₁) [/ e ] = case H [/ e ] alt₀ x altₛ x₁
  
data _↦_ {m : ℕ}{M : Subs m} : Exp 0 M → Exp 0 M → Set where
  prom : {e e' : Exp 0 M} → e ↦ e' → (H : Cxt 0 M)  → H [/ e ] ↦ H [/ e' ]

data _↦*_ {m : ℕ}{M : Subs m} : Exp 0 M → Exp 0 M → Set where
  [] : {e : Exp 0 M} → e ↦* e
  _∷_ : {e e' e'' : Exp 0 M} → e ↦ e' → e' ↦* e'' → e ↦* e''
  
Env : ℕ → Set
Env m = Σ (Subs m) (Exp 0)

emb : ∀{m} → (σ : Subs m) → (x : Fin m) → 
       (p : NatVar (lookup x σ)) → Σ (Subs m) (NatVar ∘ (lookup x))  
emb (s ∷ σ) zero p with updS s p
emb (s ∷ σ) zero p | s' , p' = s' ∷ σ , p'
emb (s ∷ σ) (suc x) p with emb σ x p
emb (s ∷ σ) (suc x) p | σ' , p' = s ∷ σ' , p'

updEnv : ∀{m} → (σ : Subs m) → (x : Fin m) → 
       (p : NatVar (lookup x σ)) → Env m
updEnv σ x p with emb σ x p
updEnv σ x p | σ' , p' = σ' , (nat (S (mvar x p')))
  
data _⇝R_ {m : ℕ} : Env m → Env m → Set where
  lift : {σ : Subs m}{e e' : Exp 0 σ} → e ↦R e' → (σ , e) ⇝R (σ , e')
  var : {σ : Subs m}{x : Fin m}{s : NatSub} → let s = lookup x σ in 
             {p : NatVar s}{a : Nat (NatVar s)} → 
             s [ p ]:= just a → 
             (σ , mvar x p) ⇝R (σ , nat (mapNat (mvar x) a))
  bind0 : {σ : Subs m}{x : Fin m}{s : NatSub} → let s = lookup x σ in 
           {p : NatVar s} → s [ p ]:= nothing → 
          (σ , mvar x p) ⇝R (repI x (updZ s p) σ , nat Z) 
  bindS : {σ : Subs m}{x : Fin m}{s : NatSub} → let s = lookup x σ in 
    {p : NatVar s} → s [ p ]:= nothing → 
    (σ , mvar x p) ⇝R updEnv σ x p

data _≤N_ : NatSub → NatSub → Set where
  ≤hole : {s : NatSub} → hole ≤N s 
  ≤Z : Z ≤N Z 
  ≤S : {s s' : NatSub} → s ≤N s' → S s ≤N S s'
  
data _≤s_ : {m : ℕ} → Subs m → Subs m → Set where
  ≤[] : _≤s_ [] []
  ≤∷ : ∀{m s s'}{σ σ' : Subs m} → s ≤N s' → σ ≤s σ' → 
                                        (s ∷ σ) ≤s (s' ∷ σ')
                                        

