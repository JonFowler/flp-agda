module num where

open import Data.Product
open import Data.Vec
open import Data.Maybe as M
open import Data.Fin hiding (_+_ ) hiding (lift)
open import Data.Nat 
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
  
data _[_↦_] : (s : NatSub) → (NatVar s) → Maybe (Nat (NatVar s)) → Set where 
  hereZ : Z [ here ↦ just Z ]
  hereS : {a : NatSub} → S a [ here ↦ just (S (there here)) ]
  there : {s : NatSub}{p : NatVar s}{n : Maybe (Nat (NatVar s))} → 
          s [ p ↦  n ] → S s [ there p ↦ M.map (mapNat there) n ]
  
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
  
data _⇝R_ {m : ℕ} : Env m → Env m → Set where
  lift : {σ : Subs m}{e e' : Exp 0 σ} → e ↦R e' → (σ , e) ⇝R (σ , e')
  
