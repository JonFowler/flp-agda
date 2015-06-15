module Subs where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Data.Nat
open import Data.Fin
open import Relation.Nullary 

 
data VarSet : Set where
  ∅ : VarSet
  V1 : VarSet
  _∪_ : VarSet → VarSet → VarSet
  
data Var : VarSet → Set where
  here : Var V1
  inL : {X Y : VarSet} → (x : Var X) → Var (X ∪ Y)
  inR : {X Y : VarSet} → (x : Var Y) → Var (X ∪ Y)

  
data Val (X : VarSet) : Set where
  fvar : (x : Var X) → Val X
  Z : Val X 
  S : Val X → Val X

Empty : VarSet → Set
Empty V = ¬ (Var V)

Empty? : (V : VarSet) → Dec (Empty V)
Empty? ∅ = yes (λ ())
Empty? V1 = no (λ ¬e → ¬e here) 
Empty? (X ∪ Y) with Empty? X | Empty? Y 
Empty? (X ∪ Y) | yes p1 | yes p2 = yes (λ {(inL x) → p1 x ; (inR y) → p2 y})
Empty? (X ∪ Y) | yes p | no ¬p = no (λ ¬e → ¬p (λ x → ¬e (inR x)))
Empty? (X ∪ Y) | no ¬p | b = no (λ ¬e → ¬p (λ x → ¬e (inL x)))

_⇀_ : VarSet → VarSet → Set
_⇀_ M N = Var M → Val N

_>>=_ : {X Y : VarSet} →  Val X → (X ⇀ Y) → Val Y
fvar x >>= f = f x
Z >>= f = Z
S a >>= f = S (a >>= f)

_>=>_ : {X Y Z : VarSet} → (X ⇀ Y) → (Y ⇀ Z) → X ⇀ Z
_>=>_ f g a = f a >>= g

return : {X : VarSet} → (x : Var X) → Val X
return = fvar

>>=-left : {X Y : VarSet} → (x : Var X) → (f : (X ⇀ Y)) → return x >>= f ≡ f x
>>=-left x f = refl

>>=-right : {X : VarSet} → (a : Val X) → a >>= return ≡ a
>>=-right (fvar x) = refl
>>=-right Z = refl
>>=-right (S a) = cong S (>>=-right a) 

>>=-assoc : {X Y Z : VarSet} → (a : Val X) → (f : X ⇀ Y) → (g : Y ⇀ Z) → 
             (a >>= f) >>= g ≡ a >>= (λ a → (f a >>= g))
>>=-assoc (fvar x) f g = refl
>>=-assoc Z f g = refl
>>=-assoc (S a) f g = cong S (>>=-assoc a f g)

_[_//_] : (X : VarSet) → (x : Var X) → VarSet → VarSet
∅ [ () // Y ]
V1 [ here // Y ] = Y
(X1 ∪ X2) [ inL x // Y ] = (X1 [ x // Y ]) ∪ X2
(X1 ∪ X2) [ inR x // Y ] =  X1 ∪ (X2 [ x // Y ])

_/_ : {X Y : VarSet} → (x : Var X) → Val Y → Var X → Val (X [ x // Y ]) 
_/_ here a here = a
_/_ (inL x) a (inL y) = (x / a) y >>= (fvar ∘ inL)
_/_ (inR x) a (inL y) = fvar (inL y)
_/_ (inL x) a (inR y) = fvar (inR y)
_/_ (inR x) a (inR y) = (x / a) y >>= (fvar ∘ inR) 

data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {∅} Z
   bindS : MinVal {V1} (S (fvar here))

data MinSub {X : VarSet} : {Y : VarSet} → X ⇀ Y → Set where 
  


--bindX : ∀{M} (x : Fin (suc M)) → Val (Fin M) → Val (Fin (suc M)) → Val (Fin M)
--bindX = {!!}
--
----data Bind : (M ⇀ N) → Set where
--
--_=<<V_ : ∀{M N} → M ⇀V N → (e : Val M) → Val N 
--f =<<V Z = Z
--f =<<V S e = S (f =<<V e)
--f =<<V fvar x = f x
--
--returnV : ∀{M} → M → Val M
--returnV p = fvar p 
--
--=<<V-left : ∀{M} → (a : Val M) → (returnV =<<V a) ≡ a
--=<<V-left Z = refl
--=<<V-left (S e) = cong S (=<<V-left e)
--=<<V-left (fvar x) = refl
--
--=<<V-right : ∀{M N : Set} → (f : M ⇀V N)
--          → (x : M) → f =<<V (returnV x) ≡ f x   
--=<<V-right f x = refl 
--
--=<<V-assoc : ∀{M N O} → 
--            (f : M ⇀V N) → (g : N ⇀V O) → (e : Val M) → 
--           (g =<<V (f =<<V e)) ≡ (λ x → g =<<V (f x)) =<<V e
--=<<V-assoc f g Z = refl
--=<<V-assoc f g (S e) = cong S (=<<V-assoc f g e)
--=<<V-assoc f g (fvar x) = refl
--
--
--
--
