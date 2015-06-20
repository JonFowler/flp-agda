module Subs where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Relation.Nullary 

postulate ext : {A B : Set}{f g : A → B} →  ((x : A) → f x ≡ g x) → f ≡ g
 
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
_⇀_ X Y = Var X → Val Y

Inp : VarSet → Set
Inp X = Var X → Val ∅

⇀-id : ∀{X} → X ⇀ X
⇀-id x = fvar x

coll : ∀{Y} → Empty Y → Var Y → Var ∅
coll p x = ⊥-elim (p x)

_>>=_ : {X Y : VarSet} →  Val X → (X ⇀ Y) → Val Y
fvar x >>= f = f x
Z >>= f = Z
S a >>= f = S (a >>= f)

collapse : ∀{X Y} → X ⇀ Y → Empty Y → X ⇀ ∅
collapse τ p x = τ x >>= (fvar ∘ coll p)

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

_/_ : {X Y : VarSet} → (x : Var X) → Val Y → X ⇀ (X [ x // Y ]) 
_/_ here a here = a
_/_ (inL x) a (inL y) = (x / a) y >>= (λ a → fvar (inL a)) 
_/_ (inR x) a (inL y) = fvar (inL y)
_/_ (inL x) a (inR y) = fvar (inR y)
_/_ (inR x) a (inR y) = (x / a) y >>= (fvar ∘ inR) 

embed : {X Y : VarSet} → (x : Var X) → Var Y → Var (X [ x // Y ]) 
embed here y = y
embed (inL x) y = inL (embed x y)
embed (inR x) y = inR (embed x y)

point-look : {X Y : VarSet} → (x : Var X) → (a : Val Y) → (x / a) x ≡ a >>= (fvar ∘ embed x)
point-look here a = sym (>>=-right a)
point-look (inL x) a = let 
  eq = cong (λ a' → a' >>= (fvar ∘ inL)) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (fvar ∘ inL))
point-look (inR x) a = let 
  eq = cong (λ a' → a' >>= (fvar ∘ inR)) (point-look x a)
    in trans eq (>>=-assoc a (fvar ∘ embed x) (fvar ∘ inR))

data MinVal : {X : VarSet} → Val X → Set where
   bindZ : MinVal {∅} Z
   bindS : MinVal {V1} (S (fvar here))
   
data LNarr {X : VarSet} (x : Var X) : {Y : VarSet} → X ⇀ Y → Set where
   narr : ∀{Y} {a : Val Y} → MinVal a → LNarr x (x / a)

--LNarr : {V : ℕ}{X : VarSet} → (x : Var X) → {Y : VarSet} → (X ⇀ Y) → Set
--LNarr x {Y}  = {!!}

_⊑ₚ_ : ∀{X Y} → Val X → Val Y → Set 
n ⊑ₚ m = ∃ (λ σ → m ≡ n >>= σ)

_⊑_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊑ τ = ∃ (λ σ' → τ ≡ σ >=> σ')

_⊏_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
σ ⊏ τ = σ ⊑ τ × ¬ (τ ⊑ σ)

_[|_//_] : ∀ {X Y Z} → (τ : X ⇀ Z) → (x : Var X) →  Y ⇀ Z → X [ x // Y ] ⇀ Z 
_[|_//_] τ here σ v = σ v
_[|_//_] τ (inL x) σ (inL x') = ((λ a → τ (inL a)) [| x // σ ]) x' 
_[|_//_] τ (inL x) σ (inR x') = τ (inR x')
_[|_//_] τ (inR x) σ (inL x') = τ (inL x')
_[|_//_] τ (inR x) σ (inR x') = ((τ ∘ inR) [| x // σ ]) x'

point-eq : ∀{ X Y Z} → (a : Val Y) → (b : Val Z) → (τ : X ⇀ Z) → (x : Var X) → τ x ≡ b → (o : a ⊑ₚ b) → (x' : Var X) → τ x' ≡ ((x / a) >=> (τ [| x // proj₁ o ])) x'
point-eq a .(τ here) τ here refl (σ , eq') here = eq'
point-eq a b τ (inL x) eq o (inL x') = let 
  r = point-eq a b (λ a → (τ (inL a))) x eq o x' 
  eq2 =  sym (>>=-assoc ((x / a) x') (λ z → fvar (inL z)) (τ [| inL x // proj₁ o ])) 
    in trans r eq2 
point-eq a b τ (inL x) eq o (inR x') = refl
point-eq a b τ (inR x) eq o (inL x') = refl
point-eq a b τ (inR x) eq o (inR x') = let 
  r = point-eq a b (λ a → (τ (inR a))) x eq o x' 
  eq2 =  sym (>>=-assoc ((x / a) x') (λ z → fvar (inR z)) (τ [| inR x // proj₁ o ])) 
    in trans r eq2 

complete-narr : ∀ {X} → (τ : Inp X) → (x : Var X) → ∃₂ (λ Y σ → LNarr x {Y} σ × σ ⊑ τ)
complete-narr τ x with τ x | inspect τ x
complete-narr τ x | fvar () | eq
complete-narr {X} τ x | Z | [ eq ] = let ab = ((λ { () }) , refl)
  in X [ x // ∅ ] , x / Z , narr bindZ , τ [| x // proj₁ ab ] , ext (point-eq Z Z τ x eq ab)
complete-narr {X} τ x | S c | [ eq ] = let ab = (λ {here → c}) , refl 
  in X [ x // V1 ] , x / (S (fvar here)) , narr bindS , τ [| x // proj₁ ab ] , ext (point-eq (S (fvar here)) (S c) τ x eq ab)
  
point-adv : ∀{X Y} → (x : Var X)  → (a : Val Y) → ((y : Var Y) → a ≠ fvar y)  →  ¬ ((x / a) ⊑ return)
point-adv x (fvar y) ne (σ , eq) = ⊥-elim (ne y refl)  
point-adv x Z ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x Z) (cong (λ f → f x) eq)
point-adv x Z ne (σ , eq) | ()
point-adv x (S a) ne (σ , eq) with subst (λ p → return x ≡ p >>= σ) (point-look x (S a)) (cong (λ f → f x) eq)
point-adv x (S a) ne (σ , eq) | ()

_≤_ : ∀{X Y Z} → X ⇀ Z → Y ⇀ Z → Set
τ' ≤ τ = ∃ (λ σ → τ ≡ σ >=> τ')

_<_ : ∀{X Y Z} → X ⇀ Z → Y ⇀ Z → Set
τ' < τ = (τ' ≤ τ) × ¬ (τ ≤ τ')

data Acc {X : VarSet} (τ : Inp X) : Set where
  acc : (∀{Y} (τ' : Inp Y) → (τ' < τ) → Acc τ') →  Acc τ
  
aux : ∀{X} → (τ : Inp X) → {Y : VarSet} (τ' : Inp Y) → (τ' < τ) → Acc τ'
aux {∅} ._ τ' ((σ , refl) , nlt) = ⊥-elim (nlt (τ' , {!!}))
aux {V1} ._ τ' ((σ , refl) , nlt) with σ here 
aux {V1} ._ τ' ((σ , refl) , nlt) | fvar x = {!!}
aux {V1} ._ τ' ((σ , refl) , nlt) | Z = acc (λ τ'' x → {!!})
aux {V1} ._ τ' ((σ , refl) , nlt) | S c = {!!}
aux {X ∪ X₁} τ τ' ((σ , eq) , nlt) = {!!}



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
