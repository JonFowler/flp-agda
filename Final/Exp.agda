module Exp where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Subs

data Exp (V : ℕ) (X : VarSet) : Set where
  Z : Exp V X 
  S :  Exp V X → Exp V X
  var : Fin V → Exp V X 
  fvar : (x : Var X) → Exp V X
  case_alt₀_altₛ_ : (e : Exp V X) → (e₀ : Exp V X) → (eₛ : Exp (suc V) X) → Exp V X
  
embed : ∀{V X} → Val X → Exp V X
embed (fvar x) = fvar x
embed Z = Z
embed (S a) = S (embed a)

sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : ∀{V' X}(V : ℕ) → Exp (V + V') X → Exp (V + suc V') X
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (fvar x) = fvar x
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

rep : ∀{V' X} (V : ℕ) → Exp (V + suc V') X → Exp V' X → Exp (V + V') X
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (fvar a) ef = fvar a
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

_⟪_⟫ : ∀{V X} → Exp (suc V) X → Exp V X → Exp V X
_⟪_⟫ = rep 0

data _↦_ {V : ℕ}{X : VarSet} : Exp V X → Exp V X → Set where
  caseZ :  (e₀ : Exp V X) → (eₛ : Exp (suc V) X) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V X) → (e₀ : Exp V X) → (eₛ : Exp (suc V) X)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : {e e' e₀ : Exp V X}{eₛ : Exp (suc V) X} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
data _↦*_ {V : ℕ}{X : VarSet} : Exp V X → Exp V X → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
 
 
--_⇀_ : Set → Set → Set
--_⇀_ X N = {V' : ℕ} → X → Exp V' N

_⟦_⟧ : ∀{V X Y} →  (e : Exp V X) → X ⇀ Y → Exp V Y
Z ⟦ σ ⟧ = Z
S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
var x ⟦ σ ⟧ = var x
fvar x ⟦ σ ⟧ = embed (σ x)
(case e alt₀ e₀ altₛ eₛ) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₀ ⟦ σ ⟧ altₛ eₛ ⟦ σ ⟧ 

⟦⟧-id : ∀{V X} → (e : Exp V X) → e ⟦ return ⟧ ≡ e
⟦⟧-id Z = refl
⟦⟧-id (S e) = cong S (⟦⟧-id e)
⟦⟧-id (var x) = refl
⟦⟧-id (fvar x) = refl
⟦⟧-id (case e alt₀ e₀ altₛ eₛ) = cong₃ case_alt₀_altₛ_ (⟦⟧-id e) (⟦⟧-id e₀) (⟦⟧-id eₛ)

⟦⟧-var :  ∀{V X Y} → (x : Var X) → (σ : X ⇀ Y)
          → _⟦_⟧ {V} (fvar x) σ ≡ embed (σ x)
⟦⟧-var x f = refl

embed-func : ∀{V X Y} → (a : Val X) → (σ : X ⇀ Y) → embed {V} a ⟦ σ ⟧ ≡ embed (a >>= σ)
embed-func (fvar x) σ = refl
embed-func Z σ = refl
embed-func (S a) σ = cong S (embed-func a σ)

⟦⟧-func :  ∀{V X Y Z} → (e : Exp V X) → (σ : X ⇀ Y) → (σ' : Y ⇀ Z) 
        → e ⟦ σ ⟧ ⟦ σ' ⟧ ≡ e ⟦ σ >=> σ' ⟧
⟦⟧-func Z σ σ' = refl
⟦⟧-func (S e) σ σ' = cong S (⟦⟧-func e σ σ')
⟦⟧-func (var x) σ σ' = refl
⟦⟧-func (fvar x) σ σ' = embed-func (σ x) σ'
⟦⟧-func (case e alt₀ e₁ altₛ e₂) σ σ' = cong₃ case_alt₀_altₛ_ (⟦⟧-func e σ σ') (⟦⟧-func e₁ σ σ') (⟦⟧-func e₂ σ σ')

