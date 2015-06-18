module Subs where

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Helpful
open import Data.Empty
open import Function
open import Data.Nat
open import Data.Fin
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
  S : (a : Val X) → Val X
  
data _⇀_ : VarSet → VarSet → Set where
  Emp : ∅ ⇀ ∅ 
  V1 : (a : Val V1) → V1 ⇀ V1
  V1Emp : (a : Val ∅) → V1 ⇀ ∅
  _,_ : ∀{X X' Y Y'} → X ⇀ Y → X' ⇀ Y' → (X ∪ X') ⇀ (Y ∪ Y')
  
_>>=_ : {X Y : VarSet} → Val X → (Var X → Val Y) → Val Y
fvar x >>= f = f x
Z >>= f = Z
S a >>= f = S (a >>= f)
  
_<$>_ : ∀{X Y} → (Var X → Var Y) → Val X → Val Y
_<$>_ f a = a >>= (fvar ∘ f)

>>=-right : {X : VarSet} → (a : Val X) → a >>= fvar ≡ a
>>=-right {X} (fvar x) = refl
>>=-right Z = refl
>>=-right (S a) = cong S (>>=-right a) 

heref : {A : Set} → (a : A) → Var V1 → A
heref a _ = a

>>=-right-spec : (a : Val V1) → a >>= (heref (fvar here)) ≡ a
>>=-right-spec (fvar here) = refl 
>>=-right-spec Z = refl
>>=-right-spec (S a) = cong S (>>=-right-spec a) -- (>>=-right a) 

>>=-assoc : {X Y Z : VarSet} → (a : Val X) → (f : Var X → Val Y) → (g : Var Y → Val Z) → 
             (a >>= f) >>= g ≡ a >>= (λ a → (f a >>= g))
>>=-assoc (fvar x) f g = refl
>>=-assoc Z f g = refl
>>=-assoc (S a) f g = cong S (>>=-assoc a f g)

lookup : ∀{X Y} → X ⇀ Y → Var X → Val Y
lookup Emp ()
lookup (V1 a) here = a 
lookup (V1Emp a) here = a
lookup (σ , σ') (inL x) = inL <$> lookup σ x
lookup (σ , σ') (inR x) = inR <$> lookup σ' x

Empty : VarSet → Set
Empty V = ¬ (Var V)

Empty? : (V : VarSet) → Dec (Empty V)
Empty? ∅ = yes (λ ())
Empty? V1 = no (λ ¬e → ¬e here) 
Empty? (X ∪ Y) with Empty? X | Empty? Y 
Empty? (X ∪ Y) | yes p1 | yes p2 = yes (λ {(inL x) → p1 x ; (inR y) → p2 y})
Empty? (X ∪ Y) | yes p | no ¬p = no (λ ¬e → ¬p (λ x → ¬e (inR x)))
Empty? (X ∪ Y) | no ¬p | b = no (λ ¬e → ¬p (λ x → ¬e (inL x)))

--coll : ∀{Y} → Empty Y → Var Y → Var ∅
--coll p x = ⊥-elim (p x)
--
--collapse : ∀{X Y} → X ⇀ Y → Empty Y → X ⇀ ∅
--collapse τ p x = τ x >>= (fvar ∘ coll p)

--
_>=>_ : {X Y Z : VarSet} → (X ⇀ Y) → (Y ⇀ Z) → X ⇀ Z
Emp >=> Emp = Emp
V1 a >=> V1 a' = V1 (a >>= heref a') 
V1 a >=> V1Emp a' = V1Emp (a >>= heref a') 
V1Emp a >=> Emp = V1Emp a
(σ , σ') >=> (τ , τ') = (σ >=> τ) , (σ' >=> τ')

return : ∀{X} → X ⇀ X
return {∅} = Emp
return {V1} = V1 (fvar here) 
return {X ∪ X₁} = return , return

>=>-right : {X Y : VarSet} → (σ : (X ⇀ Y)) → σ >=> (return {Y}) ≡ σ 
>=>-right Emp = refl
>=>-right {V1}{V1} (V1 a) = cong V1 (>>=-right-spec a) -- cong V1 {!>>=-right!} 
>=>-right (V1Emp a) = refl
>=>-right (σ , σ') = cong₂ _,_ (>=>-right σ) (>=>-right σ') 

>=>-left : {X Y : VarSet} → (σ : (X ⇀ Y)) → return >=> σ ≡ σ 
>=>-left Emp = refl
>=>-left (V1 a) = refl
>=>-left (V1Emp a) = refl
>=>-left (σ , σ') = cong₂ _,_ (>=>-left σ) (>=>-left σ') 

>=>-assoc : {X Y Z A : VarSet} → (f : X ⇀ Y) → (g : Y ⇀ Z) → (h : Z ⇀ A) →
             (f >=> g) >=> h ≡ f >=> (g >=> h) 
>=>-assoc Emp Emp Emp = refl
>=>-assoc (V1 a) (V1 a₁) (V1 a₂) = cong V1  (>>=-assoc a (λ _ → a₁) (λ _ → a₂))
>=>-assoc (V1 a) (V1 a₁) (V1Emp a₂) = cong V1Emp (>>=-assoc a (heref a₁) (heref a₂))
>=>-assoc (V1 a) (V1Emp a₁) Emp = refl
>=>-assoc (V1Emp a) Emp Emp = refl
>=>-assoc (f , f₁) (g , g₁) (h , h₁) = cong₂ _,_ (>=>-assoc f g h) (>=>-assoc f₁ g₁ h₁)

_[_//_] : (X : VarSet) → (x : Var X) → VarSet → VarSet
∅ [ () // Y ]
V1 [ here // Y ] = Y
(X1 ∪ X2) [ inL x // Y ] = (X1 [ x // Y ]) ∪ X2
(X1 ∪ X2) [ inR x // Y ] =  X1 ∪ (X2 [ x // Y ])
--
--embed : ∀{X Y}{x : Var X} → Y ⇀ X [ x // Y ]
--embed {∅} {x = ()} y
--embed {V1} {x = here} y = fvar y
--embed {X ∪ X₁} {x = inL x} y = (embed {X} y) >>= (fvar ∘ inL)
--embed {X ∪ X₁} {x = inR x} y = (embed {X₁} y) >>= (fvar ∘ inR)
--

_/_ : {X Y : VarSet} → (x : Var X) → Val Y → X ⇀ (X [ x // Y ]) 
here / a = {!!}
inL x / a = {!!}
inR x / a = {!!}

--_/_ : {X Y : VarSet} → (x : Var X) → Val Y → Var X → Val (X [ x // Y ]) 
--_/_ here a here = a
--_/_ (inL x) a (inL y) = (x / a) y >>= (fvar ∘ inL)
--_/_ (inR x) a (inL y) = fvar (inL y)
--_/_ (inL x) a (inR y) = fvar (inR y)
--_/_ (inR x) a (inR y) = (x / a) y >>= (fvar ∘ inR) 
--
--data MinVal : {X : VarSet} → Val X → Set where
--   bindZ : MinVal {∅} Z
--   bindS : MinVal {V1} (S (fvar here))
--   
--point-lookup : ∀{X Y} → (x : Var X) → (a : Val Y) → (x / a) x ≡ a >>= embed {X}
--point-lookup here a = sym (>>=-right a)
--point-lookup {X ∪ X₁}{Y} (inL x) a = let r = point-lookup x a in 
--             trans (cong (λ x₁ → x₁ >>= (fvar ∘ inL)) r) (>>=-assoc a (embed {X}) (fvar ∘ inL))
--point-lookup {X ∪ X'} (inR x) a = 
--             trans (cong (λ x' → x' >>= (fvar ∘ inR)) (point-lookup x a)) 
--                         (>>=-assoc a (embed {X'}) (fvar ∘ inR))
--
--
--_⊑_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
--σ ⊑ τ = ∃ (λ σ' → τ ≡ σ >=> σ')
--
--_⊏_ : ∀{X Y Z} → X ⇀ Y → X ⇀ Z → Set
--σ ⊏ τ = σ ⊑ τ × ¬ (τ ⊑ σ)
--
--return-min : ∀{X Y} → (σ : X ⇀ Y) → return ⊑ σ
--return-min σ = σ , refl 
--
--
--
--test : return here ≡ Z → ⊥
--test () 
--
--point-bigger : ∀{X Y} → (x : Var X) → (a : Val Y) → ((y : Var Y) → a ≠ fvar y) → return ⊏ (x / a)
--point-bigger x a ne with point-lookup x a 
--...| c = (x / a , refl) , (λ {(σ , ne') → {!!}})


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
