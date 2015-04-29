module Exp where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Subs
open import VecI
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Product
open import Helpful

data Exp {m : ℕ} (V : ℕ) (M : Subs m) : Set where
  Z : Exp V M 
  S : Exp V M → Exp V M
  var : Fin V → Exp V M 
  mvar : (x : Fin m) → (p : Holes (lookup x M))  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M 
  
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)
  
sucExp : ∀{m}{V' : ℕ}{M : Subs m}(V : ℕ) → Exp (V + V') M → Exp (V + suc V') M
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x p) = mvar x p
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂
  
sub : {V' m : ℕ}{M : Subs m} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
sub V Z ef = Z
sub V (S x) ef = S (sub V x ef)
sub zero (var zero) ef = ef
sub zero (var (suc x)) ef = var x
sub (suc V) (var zero) ef = var zero
sub (suc V) (var (suc x)) ef with sub V (var x) ef
... | e' = sucExp 0 e'
sub V (mvar x p) ef = mvar x p
sub V (case e alt₀ e₁ altₛ e₂) ef = case sub V e ef alt₀ sub V e₁ ef altₛ sub (suc V) e₂ ef

_⟪_⟫ : {V m : ℕ}{M : Subs m} → Exp (suc V) M → Exp V M → Exp V M
_⟪_⟫ = sub 0

data _↦_ {V m : ℕ}{M : Subs m} : Exp V M → Exp V M → Set where
  caseZ :  (e₀ : Exp V M) → (eₛ : Exp (suc V) M) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V M) → (e₀ : Exp V M) → (eₛ : Exp (suc V) M)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : ∀{e e' e₀ eₛ} → e ↦ e' → case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
  
data Star {A : Set}(P : A → Set)(Q : {a a' : A} → P a → P a' → Set) : {b b' : A} → P b → P b' → Set  where
  [] : ∀{a}{e : P a} → Star P Q e e
  _∷_ : ∀{a a' a''}{e : P a}{e' : P a'}{e'' : P a''} → Q e  e' → Star P Q e' e'' → Star P Q e e''
  
Const : {A : Set} → A → Set
Const {A} _ = A

_↦*_ : ∀{V m}{M : Subs m} → Exp V M → Exp V M → Set
_↦*_ e e' = Star Const _↦_ {e} {e'} e e'
  
conv : ∀{m V}{M M' : Subs m}(x : Fin m) → (p : Holes (lookup x M)) → 
     (B : M ⇨ M') → Exp V M' 
conv {M = M} x p B with convert p (lookupI₂ x B)
conv {V = V}{M = M} x p B | t = temp t --(subst Test (sym (zipWithI-lookup x updateSub M B)) t) 
  where temp : ∀{M} → Test (lookup x M) → Exp V M
        temp (S t) = S (temp t)
        temp Z = Z
        temp (pos p) = mvar x p
        
_⟦_⟧ : ∀{m V}{M M' : Subs m} → (Exp V M) → 
     (M ⇨ M') → Exp V M' 
Z ⟦ B ⟧ = Z
S e ⟦ B ⟧ = S (e ⟦ B ⟧)
var x ⟦ B ⟧ = var x
_⟦_⟧ {V = V} (mvar x p) B = (conv x p B)
(case e alt₀ e₁ altₛ e₂) ⟦ B ⟧ = case e ⟦ B ⟧ alt₀ e₁ ⟦ B ⟧ altₛ (e₂ ⟦ B ⟧)

_⇝⟨_⟩narr⇝_ : ∀{V m}{M M' : Subs m} → Exp V M → M ⇨ M' → Exp V M' → Set
_⇝⟨_⟩narr⇝_ {V}{M = M}{M'} e B e' = e ⟦ B ⟧ ≡ e'

data _⇝⟨_⟩⇝_ {V m : ℕ}{M : Subs m} : {M' : Subs m} → Exp V M → M ⇨ M' → Exp V M' → Set where
  bindZ : ∀{x p} →  mvar x p ⇝⟨ bindingZ x p ⟩⇝ mvar x p ⟦ bindingZ x p ⟧ 
  bindS : ∀{x p} →  mvar x p ⇝⟨ bindingS x p ⟩⇝ mvar x p ⟦ bindingS x p ⟧
  prom : {M' : Subs m}{B : M ⇨ M'}{e e₀ : Exp V M}{eₛ : Exp (suc V) M}{e' : Exp V M'} 
               →  e ⇝⟨ B ⟩⇝ e' → 
               case e alt₀ e₀  altₛ eₛ ⇝⟨ B ⟩⇝ case e' alt₀ e₀  ⟦ B ⟧ altₛ eₛ ⟦ B ⟧
               
isNarrowing : ∀{m V}{M M' : Subs m}{B : M ⇨ M'}{e : Exp V M}{e' : Exp V M'} 
            → e ⇝⟨ B ⟩⇝ e' → e ⇝⟨ B ⟩narr⇝ e'
isNarrowing bindZ = refl
isNarrowing bindS = refl
isNarrowing (prom r) = cong₃ case_alt₀_altₛ_ (isNarrowing r) refl refl
--  bindZ : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
--           {p : SubVar} → s [ p ]:= hole → 
--          (σ , mvar x p) ⇝M (update x (updateS Z p) σ , Z) 
--  bindS : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
--    {p : SubVar} → s [ p ]:= hole → 
--    (σ , mvar x p) ⇝M (update x (updateS (S hole) p) σ , S (mvar x (there p)))
 



