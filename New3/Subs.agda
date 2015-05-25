module Subs where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Data.Nat
open import Data.Fin
open import Relation.Nullary 

data Val (M : Set) : Set where
  mvar : (x : M) → Val M 
  Z : Val M 
  S : Val M → Val M
  
data Vars : Set where
  emp : Vars
  var : Vars
  _,_ : Vars → Vars → Vars

data Pos : Vars → Set where
  here : Pos var
  inL : ∀{V V'} → Pos V → Pos (V , V')
  inR : ∀{V V'} → Pos V' → Pos (V , V')
  
Empty : Vars → Set
Empty V = ¬ (Pos V)

Empty? : (V : Vars) → Dec (Empty V)
Empty? emp = yes (λ ())
Empty? var = no (λ z → z here)
Empty? (V , V₁) with Empty? V | Empty? V₁
Empty? (V , V₁) | yes p | yes p₁ = yes (λ {(inL x) → p x ; (inR y) → p₁ y})
Empty? (V , V₁) | yes p | no ¬p = no (λ z → ¬p (λ z₁ → z (inR z₁)))
Empty? (V , V₁) | no ¬p | d = no (λ z → ¬p (λ z₁ → z (inL z₁)))
  
Rename : ℕ → ℕ → Set
Rename M N = Fin M → Fin N

extend' : ∀{M N} → Rename M N → Rename (suc M) (suc N)
extend' f zero = zero
extend' f (suc a) = suc (f a)

 
_⇀V_ : Set → Set → Set
_⇀V_ M N = M → Val N

bindX : ∀{M} (x : Fin (suc M)) → Val (Fin M) → Val (Fin (suc M)) → Val (Fin M)
bindX = {!!}

--data Bind : (M ⇀ N) → Set where

_=<<V_ : ∀{M N} → M ⇀V N → (e : Val M) → Val N 
f =<<V Z = Z
f =<<V S e = S (f =<<V e)
f =<<V mvar x = f x

returnV : ∀{M} → M → Val M
returnV p = mvar p 

=<<V-left : ∀{M} → (a : Val M) → (returnV =<<V a) ≡ a
=<<V-left Z = refl
=<<V-left (S e) = cong S (=<<V-left e)
=<<V-left (mvar x) = refl

=<<V-right : ∀{M N : Set} → (f : M ⇀V N)
          → (x : M) → f =<<V (returnV x) ≡ f x   
=<<V-right f x = refl 

=<<V-assoc : ∀{M N O} → 
            (f : M ⇀V N) → (g : N ⇀V O) → (e : Val M) → 
           (g =<<V (f =<<V e)) ≡ (λ x → g =<<V (f x)) =<<V e
=<<V-assoc f g Z = refl
=<<V-assoc f g (S e) = cong S (=<<V-assoc f g e)
=<<V-assoc f g (mvar x) = refl




