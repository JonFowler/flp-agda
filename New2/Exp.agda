module Exp where

open import Data.Product hiding (zip)
open import Data.Vec as V hiding (_∈_)
open import Data.Fin hiding (_+_ ) hiding (lift)
open import Data.Nat 
open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import VecI
open import Sub
open import Helpful

data Exp (V : ℕ) (M : ℕ) : Set where
  Z : Exp V M
  S :  Exp V M → Exp V M
  var : Fin V → Exp V M
  mvar : (x : Fin M) → (p : Pos)  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
 
data _∈E_ {V M : ℕ} : Exp V M → Subs M → Set where
  Z : ∀{σ} → Z ∈E σ
  S : ∀{e σ} → e ∈E σ → S e ∈E σ
  var : {v : Fin V}{σ : Subs M} → var v ∈E σ
  mvar : ∀{σ}{x : Fin M}{p : Pos} → p ∈ₛ lookup x σ  → mvar x p ∈E σ
  case_alt₀_altₛ_ : ∀{e e' e'' σ} → e ∈E σ → e' ∈E σ → e'' ∈E σ → case e alt₀ e' altₛ e'' ∈E σ 

conv : ∀{V M} (x : Fin M) → (p : Pos) → (s : Sub) → Exp V M
conv x p hole = mvar x p
conv x p Z = Z
conv x p (S s) = S (conv x (there p) s)

toExp : ∀{M V} (x : Fin M) → (p : Pos) → (s : Sub) → Exp V M
toExp x p s = conv x p (lookupS p s) 



sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : {V' M : ℕ}(V : ℕ) → Exp (V + V') M → Exp (V + suc V') M
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x p) = mvar x p
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

sucExp-in : {V' M : ℕ}(V : ℕ){σ : Subs M}{e : Exp (V + V') M}
             → e ∈E σ → sucExp V e ∈E σ
sucExp-in V Z = Z 
sucExp-in V (S e₁) = S (sucExp-in V e₁ )
sucExp-in V (var) = var  
sucExp-in V (mvar x) = mvar x 
sucExp-in V (case e₁ alt₀ e₂ altₛ e₃) = case sucExp-in V e₁ alt₀ sucExp-in V e₂ altₛ sucExp-in (suc V) e₃  

sub : {V' M : ℕ} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
sub V Z ef = Z
sub V (S x) ef = S (sub V x ef)
sub zero (var zero) ef = ef
sub zero (var (suc x)) ef = var x
sub (suc V) (var zero) ef = var zero
sub (suc V) (var (suc x)) ef with sub V (var x) ef
... | e' = sucExp 0 e'
sub V (mvar x p) ef = mvar x p
sub V (case e alt₀ e₁ altₛ e₂) ef = case sub V e ef alt₀ sub V e₁ ef altₛ sub (suc V) e₂ ef

sub-in : {V' M : ℕ}(V : ℕ){σ : Subs M}{e : Exp (V + suc V') M}{e' : Exp V' M} 
             → e ∈E σ → e' ∈E σ → sub V e e' ∈E σ
sub-in V Z e'' = Z
sub-in V (S e₁) e'' = S (sub-in V e₁ e'')
sub-in zero {e = var zero} var e'' = e''
sub-in zero {e = var (suc v)} var e'' = var 
sub-in (suc V) {e = var zero} var e'' = var
sub-in (suc V) {e = var (suc v)} var e'' with sub-in V {e = var v} var e''
... | b  = sucExp-in 0 b
sub-in V (mvar x₁) e'' = mvar x₁
sub-in V (case e₁ alt₀ e₂ altₛ e₃) e'''' = case sub-in V e₁ e'''' alt₀ sub-in V e₂ e'''' altₛ
                                             sub-in (suc V) e₃ e''''

_⟪_⟫ : {V M : ℕ} → Exp (suc V) M → Exp V M → Exp V M
_⟪_⟫ = sub 0

data _↦_ {V M : ℕ} : Exp V M → Exp V M → Set where
  caseZ :  (e : Exp V M) → (e' : Exp (suc V) M) → case Z alt₀ e altₛ e' ↦ e
  caseS : {ef : Exp V M} → (e : Exp V M) → (e' : Exp (suc V) M)   
                → case (S ef) alt₀ e altₛ e' ↦ e' ⟪ ef ⟫
  prom : {e e' e₀ : Exp V M}{eₛ : Exp (suc V) M} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               

data Star {A : Set}(P : A → A → Set) : A → A → Set where
  [] : {e : A} → Star P e e
  _∷_ : {e e' e'' : A} → P e  e' → Star P e' e'' → Star P e e''
  
_↦*_ : {V M : ℕ} → Exp V M → Exp V M → Set
_↦*_ = Star _↦_

_⟦_⟧ : ∀{V M} → (e : Exp V M) → (τ : Subs M) → Exp V M
Z ⟦ σ ⟧ = Z
S e ⟦ σ ⟧ = S (e ⟦ σ ⟧)
var x ⟦ σ ⟧ = var x
mvar x p ⟦ σ ⟧ = toExp x p (lookup x σ) 
(case e alt₀ e₁ altₛ e₂) ⟦ σ ⟧ = case e ⟦ σ ⟧ alt₀ e₁ ⟦ σ ⟧ altₛ e₂ ⟦ σ ⟧

conv-over : ∀{V M} {τ : Subs M}{x : Fin M} {s s' : Sub}  (p : Pos) → (s ≤ₛ s') → s' ≡ lookupS p (lookup x τ) → conv {V = V} x p s' ≡ conv x p s ⟦ τ ⟧
conv-over {x = x} p ≤ₛ-hole eq = cong (conv x p) eq
conv-over p ≤ₛ-Z eq = refl
conv-over p (≤ₛ-S o) eq = cong S (conv-over (there p) o (there-lookupS p eq))

subs-over : ∀{V M} {σ τ : Subs M} → σ ≤s τ → (e : Exp V M) → e ⟦ τ ⟧ ≡ (e ⟦ σ ⟧) ⟦ τ ⟧
subs-over o Z = refl
subs-over o (S e) = cong S (subs-over o e)
subs-over o (var x) = refl
subs-over o (mvar x p) = conv-over p (lookupS-mono p (lookupI₂ x o)) refl 
subs-over o (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-over o e) (subs-over o e₁) (subs-over o e₂)
 


 
 

