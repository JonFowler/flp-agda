module Exp where

open import Data.Nat
open import Data.Fin hiding (_+_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function

data Exp (V : ℕ) (M : Set) : Set where
  Z : Exp V M 
  S :  Exp V M → Exp V M
  var : Fin V → Exp V M 
  mvar : (x : M) → Exp V M
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  
embed : ∀{V M} → Val M → Exp V M
embed (mvar x) = mvar x
embed Z = Z
embed (S a) = S (embed a)
 
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : ∀{V' M}(V : ℕ) → Exp (V + V') M → Exp (V + suc V') M
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x) = mvar x
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

rep : ∀{V' M} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (mvar a) ef = mvar a
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

_⟪_⟫ : ∀{V M} → Exp (suc V) M → Exp V M → Exp V M
_⟪_⟫ = rep 0

data _↦_ {V : ℕ}{M : Set} : Exp V M → Exp V M → Set where
  caseZ :  (e₀ : Exp V M) → (eₛ : Exp (suc V) M) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V M) → (e₀ : Exp V M) → (eₛ : Exp (suc V) M)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : {e e' e₀ : Exp V M}{eₛ : Exp (suc V) M} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
data _↦*_ {V : ℕ}{M : Set} : Exp V M → Exp V M → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
 
 
_⇀_ : Set → Set → Set
_⇀_ M N = {V' : ℕ} → M → Exp V' N

_=<<_ : ∀{V M N} → M ⇀ N → (e : Exp V M) → Exp V N 
f =<< Z = Z
f =<< S e = S (f =<< e)
f =<< var x = var x
f =<< mvar x = f x
_=<<_ {V = V} f (case e alt₀ e₁ altₛ e₂) = case f =<< e alt₀ f =<< e₁ altₛ _=<<_ {V = suc V} f e₂ 

return : ∀{V M} → M → Exp V M
return p = mvar p 

=<<-left : ∀{V M} → (e : Exp V M) → (return =<< e) ≡ e
=<<-left Z = refl
=<<-left (S e) = cong S (=<<-left e)
=<<-left (var x) = refl
=<<-left (mvar x) = refl
=<<-left (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<-left e) (=<<-left e₁) (=<<-left e₂)

=<<-right : ∀{V}{M N : Set} → (f : M ⇀ N)
          → (x : M) → _=<<_ f (return x) ≡ f {V} x   
=<<-right f x = refl 


=<<-assoc : ∀{V M N O} → 
            (f : M ⇀ N) → (g : N ⇀ O) → (e : Exp V M) → 
           (g =<< (f =<< e)) ≡ (λ x → g =<< (f x)) =<< e
=<<-assoc f g Z = refl
=<<-assoc f g (S e) = cong S (=<<-assoc f g e)
=<<-assoc f g (var x) = refl
=<<-assoc f g (mvar x) = refl
=<<-assoc f g (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<-assoc f g e) (=<<-assoc f g e₁) (=<<-assoc f g e₂) 

_=<<V_ : ∀{V M N} → M ⇀V N → (e : Exp V M) → Exp V N 
f =<<V e = (embed ∘ f) =<< e

=<<V-assoc : ∀{V M N O} → 
            (f : M ⇀V N) → (g : N ⇀V O) → (e : Exp V M) → 
           (g =<<V (f =<<V e)) ≡ (λ x → g =<<V (embed (f x))) =<< e
=<<V-assoc f g Z = refl
=<<V-assoc f g (S e) = cong S (=<<V-assoc f g e)
=<<V-assoc f g (var x) = refl
=<<V-assoc f g (mvar x) = refl
=<<V-assoc f g (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<V-assoc f g e) (=<<V-assoc f g e₁) (=<<V-assoc f g e₂) 

_∘V_ : ∀{M N O} → N ⇀ O → M ⇀ N →  M ⇀ O
_∘V_ = {!!}


data _⇥_ {V : ℕ}{M : Set} : Exp V M → M → Set where
    susp : (x : M) → mvar x ⇥ x
    subj-susp : ∀{e e₀ eₛ x} → e ⇥ x → case e alt₀ e₀ altₛ eₛ ⇥ x
 
 
NSet-complete : {M N : Set} → (B : (M → Val N) → Set) → Set
NSet-complete {M} B = {V : ℕ} → (B' : M → Val ⊥) → {!!}
