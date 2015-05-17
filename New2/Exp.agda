module Exp where

open import Data.Product hiding (zip)
open import Data.Vec as V hiding (_∈_)
open import Data.Fin hiding (_+_ ) hiding (lift) hiding (_≤_) hiding (_<_)
open import Data.Nat hiding (_≤_) hiding (_<_)
open import Function
open import Data.Unit hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import VecI
open import Sub
open import Helpful

MVar : ∀{m} (σ : Subs m) → Set
MVar {m} σ = Σ (Fin m) (λ x → Pos (lookup x σ))

data Exp {M : ℕ} (V : ℕ) (σ : Subs M) : Set where
  Z : Exp V σ 
  S :  Exp V σ → Exp V σ
  var : Fin V → Exp V σ 
  mvar : MVar σ  → Exp V σ 
  case_alt₀_altₛ_ : Exp V σ → Exp V σ → Exp (suc V) σ → Exp V σ
 
fromValPos : ∀{m V}{σ : Subs m} → (x : Fin m) → ValPos (lookup x σ) → Exp V σ
fromValPos x (pos p) = mvar (x , p)
fromValPos x Z = Z
fromValPos x (S vp) = S (fromValPos x vp)
‌

sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : ∀{V' m}{σ : Subs m}(V : ℕ) → Exp (V + V') σ → Exp (V + suc V') σ
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x) = mvar x
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

rep : {V' m : ℕ}{σ : Subs m} (V : ℕ) → Exp (V + suc V') σ → Exp V' σ → Exp (V + V') σ
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (mvar x) ef = mvar x 
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

_⟪_⟫ : {m V : ℕ}{σ : Subs m} → Exp (suc V) σ → Exp V σ → Exp V σ
_⟪_⟫ = rep 0

data _↦_ {m V : ℕ}{σ : Subs m} : Exp V σ → Exp V σ → Set where
  caseZ :  (e₀ : Exp V σ) → (eₛ : Exp (suc V) σ) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V σ) → (e₀ : Exp V σ) → (eₛ : Exp (suc V) σ)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : {e e' e₀ : Exp V σ}{eₛ : Exp (suc V) σ} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
--↦-NoM : {m V : ℕ}{σ σ' : Subs m} → (e : Exp V σ) → (e' : Exp V σ') → 
               
data _↦*_ {m V : ℕ}{σ : Subs m} : Exp V σ → Exp V σ → Set where
  [] : ∀{e} → e ↦* e 
  _∷_ : ∀{e e' e''} → (r : e ↦ e') → (r* : e' ↦* e'') → e ↦* e''
  

_⇀_ : ∀{m} → Subs m → Subs m → Set
_⇀_ {m} σ σ' = {V : ℕ} → MVar σ → Exp V σ'

_=<<E_ : ∀{V m}{σ σ' : Subs m} → (f : σ ⇀ σ') → (e : Exp V σ) → Exp V σ' 
_=<<E_ f Z = Z
_=<<E_ f (S e) = S (f =<<E e)
_=<<E_ f (var x) = var x
_=<<E_ f (mvar x) = f x
_=<<E_ f (case e alt₀ e₁ altₛ e₂) = case f =<<E e alt₀ f =<<E e₁ altₛ (f =<<E e₂)

returnE : ∀{m}{σ : Subs m} → σ ⇀ σ 
returnE = mvar

=<<E-left : ∀{V m}{σ : Subs m} → (e : Exp V σ) → (returnE =<<E e) ≡ e
=<<E-left Z = refl
=<<E-left (S e) = cong S (=<<E-left e)
=<<E-left (var x) = refl
=<<E-left (mvar x) = refl
=<<E-left (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<E-left e) (=<<E-left e₁) (=<<E-left e₂)

=<<E-right : ∀{m V}{σ σ' : Subs m} → 
          (f : σ ⇀ σ') 
          → (x : MVar σ) → f =<<E returnE x ≡ f {V} x   
=<<E-right f x = refl

_=<<E-eq_ : ∀{V m}{σ σ' : Subs m} → 
      {f g : σ ⇀ σ'}  →
      ({V' : ℕ}(x : MVar σ) → f {V'} x ≡ g x) → 
       (e : Exp V σ) → f =<<E e ≡ g =<<E e 
_=<<E-eq_ f Z = refl
_=<<E-eq_ f (S e) = cong S (f =<<E-eq e)
_=<<E-eq_ f (var x) = refl
_=<<E-eq_ f (mvar x) = f x
_=<<E-eq_ f (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (f =<<E-eq e) (f =<<E-eq e₁) (f =<<E-eq e₂)

=<<E-func : ∀{V m}{σ σ' σ'' : Subs m} (f : σ ⇀ σ') → (g : σ' ⇀ σ'') → (e : Exp V σ) → 
           (g =<<E (f =<<E e)) ≡ (λ x → g =<<E (f x)) =<<E e
=<<E-func f g Z = refl
=<<E-func f g (S e) = cong S (=<<E-func f g e)
=<<E-func f g (var x) = refl
=<<E-func f g (mvar x) = refl
=<<E-func f g (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<E-func f g e) (=<<E-func f g e₁) (=<<E-func f g e₂)

fromValPos-func : ∀{m V}{σ σ' : Subs m} → (x : Fin m) → 
    (f : (x' : Fin m) → Pos (lookup x' σ) → ValPos (lookup x' σ')) →  (vp : ValPos (lookup x σ))
  → (λ {(x' , p') → fromValPos x' (f x' p')}) =<<E (fromValPos {V = V} x vp) ≡ fromValPos x (f x =<< vp)
fromValPos-func x f (pos p) = refl
fromValPos-func x f Z = refl
fromValPos-func x f (S vp) = cong S (fromValPos-func x f vp)


_⟦_⟧ : ∀{V m}{σ σ' : Subs m} → (e : Exp V σ) → (σ ≤ σ') → Exp V σ' 
e ⟦ σ ⟧ =  (λ {(x , p) → fromValPos x (toValPos p (lookupI₂ x σ))}) =<<E e 

⟦⟧-refl : ∀{V m}{σ : Subs m}{e : Exp V σ}(o : σ ≤ σ) → e ⟦ o ⟧ ≡ e
⟦⟧-refl {e = e} o = trans ((λ {(x , p) → cong (fromValPos x) (toValPos-refl p (lookupI₂ x o))}) =<<E-eq e) 
              (=<<E-left e)

⟦⟧-func : ∀{V m}{σ σ' σ'' : Subs m} → (e : Exp V σ) → (o : σ ≤ σ') → (o' : σ' ≤ σ'') → 
         e ⟦ o ⟧ ⟦ o' ⟧ ≡ e ⟦ o' ≤-∘ o ⟧
⟦⟧-func e o o' = 
  trans (=<<E-func (λ {(x , p) → fromValPos x (toValPos p (lookupI₂ x o))}) 
                  (λ {(x , p) → fromValPos x (toValPos p (lookupI₂ x o'))}) e) 
        ((λ {(x , p) → trans (fromValPos-func x (λ x' p' → toValPos p' (lookupI₂ x' o'))  (toValPos p (lookupI₂ x o)))
                         (cong (fromValPos x) (
                  let r = toValPos-func p (lookupI₂ x o) (lookupI₂ x o') in trans r (cong (toValPos p) (≤ₛ-uniq (lookupI₂ x o' ≤ₛ-∘ lookupI₂ x o) (lookupI₂ x (o' ≤-∘ o))))))}) 
                =<<E-eq e) 
                
⟦⟧-uniq : ∀{V m}{σ σ'  : Subs m} (e : Exp V σ)(o : σ ≤ σ')(o' : σ ≤ σ') → 
         e ⟦ o ⟧ ≡ e ⟦ o' ⟧
⟦⟧-uniq e o o' = cong (λ x → e ⟦ x ⟧) (≤-uniq o o')



data _⇥_ {m V : ℕ}{σ : Subs m} : Exp V σ → MVar σ → Set where
    susp : (x : MVar σ) → mvar x ⇥ x
    subj-susp : ∀{e e₀ eₛ x} → e ⇥ x → case e alt₀ e₀ altₛ eₛ ⇥ x
    
_[_//_] : ∀{m}(σ : Subs m) → (x : MVar σ) → (s : Sub) → Subs m
(s ∷ σ) [ zero , p // s' ] =  s [ p //ₛ s' ] ∷ σ
(s ∷ σ) [ suc x , p // s' ] = s ∷ σ [ x , p // s' ]

[//]-strict : ∀{m} (σ : Subs m) →  (x : MVar σ) → (s' : Sub) → (s' ≠ hole) → σ [ x // s' ] ≠ σ 
[//]-strict (s ∷ σ) (zero , p) s' ne eq = [//ₛ]-strict s p s' ne (down∷ eq)
[//]-strict (s ∷ σ) (suc x , p) s' ne eq = [//]-strict σ (x , p) s' ne (downl∷ eq)
    
_/_ : ∀{m}{σ : Subs m} → (x : MVar σ) → (s : Sub) → σ ≤ σ [ x // s ]
_/_ {σ = s ∷ σ} (zero , p) s' = (p /ₛ s') ∷ ≤-refl
_/_ {σ = s ∷ σ} (suc x , p) s' = ≤ₛ-refl ∷ (x , p) / s'

--data _⇝G_ {m V : ℕ}{σ σ' : Subs m} : Exp V σ → Exp V σ' → Set where 
--  narr : ∀{e} → (o : σ ≤ σ') → e ⇝G e ⟦ o ⟧
  
data MinB {m : ℕ}{σ : Subs m} (x : MVar σ) : {σ' : Subs m}  → σ ≤ σ' → Set where
  bind : ∀{s} → MinSub s →  MinB x (x / s)
  
sucMinB : ∀{m s}{σ σ' : Subs m} → (x : Fin m) → (p : Pos (lookup x σ)) → (b : σ ≤ σ') → MinB (x , p) b → MinB (suc x , p) (≤ₛ-refl {s} ∷ b)
sucMinB x p .((x , p) / _) (bind s) = bind s

--data _➣_ {m V : ℕ}{σ σ' : Subs m} : Exp V σ → (σ ≤ σ') → Set where 
--  narr : ∀{e b} → (x : MVar σ) → (s : e ⇥ x) → (MinB x b) → e ➣ b
  
--⇝N-mono : ∀{V m}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → e ⇝N e' → σ ≤ σ'
--⇝N-mono (narrZ x x₁)  =  x / Z 
--⇝N-mono (narrS x x₁)  = x / S hole
--

--⇝N-⇝G : {m V : ℕ}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → e ⇝N e' → e ⇝G e'
--⇝N-⇝G (narrZ x s) = narr (x / Z)
--⇝N-⇝G (narrS x s) = narr (x / S hole)

ExpP : Set₁
ExpP = ∀ {m V}{σ : Subs m} → Exp V σ → Set

NarrS : ExpP → Set₁
NarrS P = ∀{m V}{σ σ' : Subs m}{e : Exp V σ} → P e → σ ≤ σ' → Set


data NRed {m V : ℕ}(P : ExpP)(Q : NarrS P){σ : Subs m} :
     {σ' : Subs m} → Exp V σ → Exp V σ' → Set where 
  narr : ∀{e σ'} → (p : P e) → (b : σ ≤ σ') → Q p b → NRed P Q e (e ⟦ b ⟧)
  red : ∀{e e'} → (r : e ↦ e') → NRed P Q e e'
 
Susp : ExpP 
Susp {σ = σ} e = Σ (MVar σ) (_⇥_ e)

MinBs : NarrS Susp
MinBs (x , sx) = MinB x 

--
_⇝_ : {m V : ℕ}{σ σ' : Subs m} → Exp V σ → Exp V σ' → Set  
_⇝_ = NRed Susp MinBs
  
⇝-mono : ∀{V m}{P : ExpP}{Q : NarrS P}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → NRed P Q e e' → σ ≤ σ'
⇝-mono (narr x o b) = o -- ⇝N-mono n
⇝-mono (red x) = ≤-refl

--data _⇝F_ {m V : ℕ}{σ : Subs m} : {σ' : Subs m} → Exp V σ → Exp V σ' → Set where
--  fill : ∀{e σ' σ''}{e' : Exp V σ'} → e ⇝ e' → (o : σ' ≤ σ'') → e ⇝F e' ⟦ o ⟧
--
data NRed! {m V : ℕ}(P : ExpP)(Q : NarrS P) {σ : Subs m} : 
              {σ' : Subs m} → Exp V σ → Exp V σ' → Set  where
  [] : ∀{e σ'} → (o : σ ≤ σ') → NRed! P Q e (e ⟦ o ⟧)
  _∷_ : ∀{σ' σ'' e}{e' : Exp V σ'}{e'' : Exp V σ''} → (r : NRed P Q e e') → 
                                       (r! : NRed! P Q e' e'') → NRed! P Q e e''
--
_⇝!_ : {m V : ℕ}{σ σ' : Subs m} → Exp V σ → Exp V σ' → Set  
_⇝!_ = NRed! Susp MinBs
  

⇝!-mono : ∀{V m}{P : ExpP}{Q : NarrS P}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → NRed! P Q e e' → σ ≤ σ'
⇝!-mono ([] o) = o 
⇝!-mono (x ∷ r) = ⇝!-mono r ≤-∘ ⇝-mono x


sucExp-fromVP : {V' m : ℕ}{σ : Subs m}(V : ℕ) → (x : Fin m) →  (vp : ValPos (lookup x σ))    →  sucExp {V'} V (fromValPos x vp) ≡ fromValPos x vp
sucExp-fromVP V x (pos p) = refl
sucExp-fromVP V x Z = refl
sucExp-fromVP V x (S vp) = cong S (sucExp-fromVP V x vp)

sucExp-func : ∀{V' m}{σ σ' : Subs m}(V : ℕ) → (e : Exp (V + V') σ) → (o : σ ≤ σ') → sucExp V (e ⟦ o ⟧) ≡ sucExp V e ⟦ o ⟧
sucExp-func V Z o = refl
sucExp-func V (S e) o = cong S (sucExp-func V e o)
sucExp-func V (var x) o = refl
sucExp-func V (mvar (x , p)) o = sucExp-fromVP V x (toValPos p (lookupI₂ x o))
sucExp-func V (case e alt₀ e₁ altₛ e₂) o = cong₃ case_alt₀_altₛ_ (sucExp-func V e o) (sucExp-func V e₁ o) (sucExp-func (suc V) e₂ o) 

rep-fromVP : {V' m : ℕ}{σ : Subs m}(V : ℕ) → (e' : Exp V' σ) → (x : Fin m) →  (vp : ValPos (lookup x σ))    →  rep V (fromValPos x vp) e' ≡ fromValPos x vp
rep-fromVP V e' x (pos p) = refl
rep-fromVP V e' x Z = refl
rep-fromVP V e' x (S vp) = cong S (rep-fromVP V e' x vp)

rep-func : {V' m : ℕ}{σ σ' : Subs m}(V : ℕ) → (e : Exp (V + suc V') σ) → (e' : Exp V' σ) → (o : σ ≤ σ') →  rep V (e ⟦ o ⟧) (e' ⟦ o ⟧) ≡ (rep V e e') ⟦ o ⟧
rep-func V Z e' o = refl
rep-func V (S e) e' o = cong S (rep-func V e e' o)
rep-func zero (var zero) e' o = refl
rep-func zero (var (suc x)) e' o = refl
rep-func (suc V) (var zero) e' o = refl
rep-func (suc V) (var (suc x)) e' o with rep-func V (var x) e' o
...| p = trans (cong (sucExp 0) p) (sucExp-func zero (rep V (var x) e') o)
rep-func V (mvar (x , p)) e' o = rep-fromVP V (e' ⟦ o ⟧) x (toValPos p (lookupI₂ x o))
rep-func V (case e alt₀ e₁ altₛ e₂) e' o = cong₃ case_alt₀_altₛ_ (rep-func V e e' o) (rep-func V e₁ e' o) (rep-func (suc V) e₂ e' o)

↦-lift : ∀{m V}{σ σ' : Subs m}{e e' : Exp V σ} → e ↦ e' → (o : σ ≤ σ') → e ⟦ o ⟧ ↦ e' ⟦ o ⟧
↦-lift (caseZ e₀ eₛ) o = caseZ (e₀ ⟦ o ⟧) (eₛ ⟦ o ⟧)
↦-lift (caseS e e₀ eₛ) o = subst 
       (λ e' → ((case (S e) alt₀ e₀ altₛ eₛ) ⟦ o ⟧) ↦ e') 
       (rep-func zero eₛ e o) 
       (caseS (e ⟦ o ⟧) (e₀ ⟦ o ⟧) (eₛ ⟦ o ⟧))
↦-lift (prom r) o = prom (↦-lift r o)

↦*-lift : ∀{m V}{σ σ' : Subs m}{e e' : Exp V σ} → e ↦* e' → (o : σ ≤ σ') → e ⟦ o ⟧ ↦* e' ⟦ o ⟧
↦*-lift [] o = []
↦*-lift (x ∷ r) o = ↦-lift x o ∷ ↦*-lift r o


--⇝-sound : ∀{m V}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → (r : e e') → e ⟦ ⇝-mono r ⟧ ↦ e'
--⇝-sound (narr x o b r) = r
--⇝-sound {e' = e'} (red r) = subst (λ x → x ↦ e') (sym (⟦⟧-refl ≤-refl)) r

NRed!-sound : ∀{m V}{P : ExpP}{Q : NarrS P}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → (r : NRed! P Q e e') → e ⟦ ⇝!-mono r ⟧ ↦* e'
NRed!-sound ([] o) = []
NRed!-sound {e = e}{e'} (narr p b x ∷ r!) = coerce₁ (NRed!-sound r!) 
  where coerce₁ = subst (λ a → a ↦* e') (⟦⟧-func e b (⇝!-mono r!))
NRed!-sound {e = e}{e'} (red r ∷ r!) = coerce₁ (↦-lift r (⇝!-mono r!) ∷ NRed!-sound r!)
  where coerce₁ = subst (λ x → e ⟦ x ⟧ ↦* e') (≤-uniq (⇝!-mono r!) (⇝!-mono r! ≤-∘ ≤-refl)) 

completeNotSusp : ∀{m V}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → (b : σ ≤ σ') → e ⟦ b ⟧ ↦ e' → ¬ (Susp e) →  Σ (Exp V σ) (λ e'' → e ↦ e'' × e'' ⟦ b ⟧ ≡ e')
completeNotSusp {e = Z} b () ¬s
completeNotSusp {e = S e} b () ¬s
completeNotSusp {e = var x} b () ¬s
completeNotSusp {e = mvar x} b r ¬s = ⊥-elim (¬s (x , susp x))
completeNotSusp {e = case Z alt₀ e₁ altₛ e₂} b (caseZ ._ ._) ¬s = e₁ , caseZ e₁ e₂ , refl
completeNotSusp {e = case Z alt₀ e₁ altₛ e₂} b (prom ()) ¬s
completeNotSusp {m}{V} {e = case S e alt₀ e₁ altₛ e₂} b (caseS ._ ._ ._) ¬s = 
  e₂ ⟪ e ⟫ , caseS e e₁ e₂ , sym (rep-func zero e₂ e b)
completeNotSusp {e = case S e alt₀ e₁ altₛ e₂} b (prom ()) ¬s
completeNotSusp {e = case var x alt₀ e₁ altₛ e₂} b (prom ()) ¬s
completeNotSusp {e = case mvar x alt₀ e₁ altₛ e₂} b r ¬s = ⊥-elim (¬s (x , subj-susp (susp x)))
completeNotSusp {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  with completeNotSusp {e = case e alt₀ e₁ altₛ e₂} b r (λ {(x , sus) → ¬s (x , (subj-susp sus))})
completeNotSusp {m} {V} {σ} {σ'} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} b (prom r) ¬s 
  | e'' , r' , eq = case e'' alt₀ e₃ altₛ e₄  , prom r' , cong₃ case_alt₀_altₛ_ eq refl refl
  
decSusp : ∀{V m}{σ : Subs m} → (e : Exp V σ) → Dec (Susp e)
decSusp Z = no (λ {( x , () )} )
decSusp (S e) = no (λ {( x , () )} )
decSusp (var x) = no (λ {( x , () )} )
decSusp (mvar x) = yes (x , susp x)
decSusp (case e alt₀ e₁ altₛ e₂) with decSusp e
decSusp (case e alt₀ e₁ altₛ e₂) | yes (x , s) = yes (x , subj-susp s)
decSusp (case e alt₀ e₁ altₛ e₂) | no ¬p = no (λ {(x , subj-susp s) → ¬p (x , s)})
  

--↦-NotFromVal : ∀{m V}{σ : Subs m}{e' : Exp V σ} → (x : Fin m) → (vp : ValPos (lookup x σ)) →  ¬ (fromValPos x vp ↦ e')
--↦-NotFromVal x (pos p) ()
--↦-NotFromVal x Z ()
--↦-NotFromVal x (S vp) ()
--


NSet-complete : ∀{m} → (σ : Subs m) → (B : {σ' : Subs m} → σ ≤ σ' → Set) → Set
NSet-complete {m} σ B = {τ : Subs m} → σ ≤ τ → Inps τ → ∃₂ (λ σ' b → B {σ'} b × σ' ≤ τ )

NSet-strict : ∀{m} → (σ : Subs m) → (B : {σ' : Subs m} → σ ≤ σ' → Set) → Set
NSet-strict {m} σ B = ∀ {σ'} → (b : σ ≤ σ') → B b → σ < σ'

MinB-complete : ∀{m} {σ : Subs m} → (x : MVar σ) → NSet-complete σ (MinB x) 
MinB-complete {σ = (s ∷ σ)} (zero , p) (o ∷ os) (inp ∷ inps) with o [ₛ p ] | inspect (_[ₛ_] o) p
MinB-complete {σ = (s ∷ σ)} (zero , p) (o ∷ os) (inp ∷ inps) | hole | [ eq ] = ⊥-elim ([ₛ]-inp inp o p eq)
MinB-complete {σ = (s ∷ σ)} (zero , p) (o ∷ os) (inp ∷ inps) | Z | [ eq ] =  s [ p //ₛ Z ] ∷ σ , (p /ₛ Z) ∷ ≤-refl , bind Z , look-sub o p (subst (λ x → Z ≤ₛ x) (sym eq) ≤ₛ-Z) ∷ os
MinB-complete {σ = (s ∷ σ)} (zero , p) (o ∷ os) (inp ∷ inps) | S c | [ eq ] = s [ p //ₛ S hole ] ∷ σ , (p /ₛ S hole) ∷ ≤-refl , bind Shole , look-sub o p (subst (λ x → S hole ≤ₛ x) (sym eq) (≤ₛ-S (≤ₛ-hole c)))  ∷ os
MinB-complete {σ = (s ∷ σ)} (suc x , p) (o ∷ os) (inp ∷ inps) with MinB-complete (x , p) os inps
MinB-complete {σ = (s ∷ σ)} (suc x , p) (o ∷ os) (inp ∷ inps) | σ' , os' , bs , lt = s ∷ σ' , ≤ₛ-refl ∷ os' , sucMinB x p os' bs , o ∷ lt

MinB-strict : ∀{m}{σ : Subs m} → (x : MVar σ) → NSet-strict σ (MinB x) 
MinB-strict {σ = σ} x .(x / Z) (bind Z) = x / Z , ≠sym ([//]-strict σ x Z (λ ()))
MinB-strict {σ = σ} x .(x / S hole) (bind Shole) = x / S hole , ≠sym ([//]-strict σ x (S hole) (λ ()))
--
⇝!-complete : ∀{m V}{σ τ : Subs m}{e' : Exp V τ}(e : Exp V σ) → (o : σ ≤ τ) → Inps τ → Accs τ σ → e ⟦ o ⟧ ↦* e' → e ⇝! e' 
⇝!-complete e b inp p [] = [] b 
⇝!-complete {e' = e'} e b inp ac (r ∷ r*)  with decSusp e
⇝!-complete {e' = e'} e b inp (accs p) (r ∷ r*)  | yes (x , s) with MinB-complete x b inp
⇝!-complete {e' = e'} e b inp (accs p) (r ∷ r*)  | yes (x , s) | σ' , o , minb , b'  = 
  narr (x , s) o minb  ∷ ⇝!-complete (e ⟦ o ⟧) b' inp (p σ' b' (MinB-strict x o minb)) (coerce₁ (r ∷ r*))
    where coerce₁ = subst (λ z → z ↦* e') (trans (cong (λ z → e ⟦ z ⟧) (≤-uniq b (b' ≤-∘ o))) (sym (⟦⟧-func e o b')))
⇝!-complete e b inp ac (r ∷ r*) | no ¬p with completeNotSusp b r ¬p
⇝!-complete e b inp ac (r ∷ r*) | no ¬p | e'' , r' , refl = red r' ∷ ⇝!-complete e'' b inp ac r*


--⇝F-complete {e = Z} o ()
--⇝F-complete {e = S e} o ()
--⇝F-complete {e = var x} o ()
--⇝F-complete {e = mvar (x , p)} o r = ⊥-elim (↦-NotFromVal x (toValPos p (lookupI₂ x o)) r)
--⇝F-complete {e = case Z alt₀ e₁ altₛ e₂} o (caseZ ._ ._) = fill (red (caseZ e₁ e₂)) o
--⇝F-complete {e = case Z alt₀ e₁ altₛ e₂} o (prom ())
--⇝F-complete {e = case S e alt₀ e₁ altₛ e₂} o (caseS ._ ._ ._) = let
--       coerce₁ = subst (λ x → case S e alt₀ e₁ altₛ e₂ ⇝F x) (sym (rep-func zero e₂ e o))
--    in coerce₁ (fill (red (caseS e e₁ e₂)) o)
--⇝F-complete {e = case S e alt₀ e₁ altₛ e₂} o (prom ())
--⇝F-complete {e = case var x alt₀ e₁ altₛ e₂} o (prom ())
--⇝F-complete {e = case mvar (x , p) alt₀ e₁ altₛ e₂} o r 
--            with (toValPos p (lookupI₂ x o)) | inspect (toValPos p) (lookupI₂ x o)
--⇝F-complete {m} {V} {σ} {σ'} {._} {case mvar (x , p) alt₀ e₁ altₛ e₂} o (prom ()) | pos p₁ | eq
--⇝F-complete {m} {V} {σ} {σ'} {._} {case mvar (x , p) alt₀ e₁ altₛ e₂} o (caseZ ._ ._) | Z | [ eq ] =
--  let b = (x , p) / Z
--      s = subj-susp {e₀ = e₁}{e₂} (susp (x , p)) 
--      r' = narr (x , p) {s} b  bindZ {!!} -- (caseZ (e₁ ⟦ b ⟧) (e₂ ⟦ b ⟧))
--  in {!!}
--⇝F-complete {m} {V} {σ} {σ'} {._} {case mvar (x , p) alt₀ e₁ altₛ e₂} o (prom ()) | Z | eq
--⇝F-complete {m} {V} {σ} {σ'} {._} {case mvar (x , p) alt₀ e₁ altₛ e₂} o (caseS .(fromValPos x c) ._ ._) | S c | [ eq ] = {!!}
--⇝F-complete {m} {V} {σ} {σ'} {._} {case mvar (x , p) alt₀ e₁ altₛ e₂} o (prom ()) | S c | eq
--⇝F-complete {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r)  with ⇝F-complete {e = case e alt₀ e₁ altₛ e₂} o r
--⇝F-complete {m} {V} {σ} {σ'} {._} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r) 
--  | fill (narr {e' = e'} x {s} o' b r') o₁ = coerce₁ (fill (narr x {s'} o' b promr) o₁) 
--    where
--      s' = subj-susp {e₀ = e₃}{eₛ = e₄} s
--      promr = prom {e₀ = e₃ ⟦ o' ⟧} {eₛ = e₄ ⟦ o' ⟧} r'
--      coerce₁ = subst₂ (λ x₁ x₂ → 
--                (case (case e alt₀ e₁ altₛ e₂) alt₀ e₃ altₛ e₄) ⇝F  case e' ⟦ o₁ ⟧ alt₀ x₁ altₛ x₂) 
--                (trans (⟦⟧-func e₃ o' o₁) (⟦⟧-uniq e₃ (o₁ ≤-∘ o') o)) 
--                (trans (⟦⟧-func e₄ o' o₁) (⟦⟧-uniq e₄ (o₁ ≤-∘ o') o))
--
--⇝F-complete {m} {V} {σ} {σ'} {._} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r) 
--  | fill (red r') o₁ with ≤-uniq o o₁
--⇝F-complete {m} {V} {σ} {σ'} {._} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r) 
--  | fill (red r') .o | refl = fill (red (prom r')) o 

--⇝!-complete : ∀{m V}{σ σ' : Subs m}{e' : Exp V σ'}{e : Exp V σ} → (o : σ ≤ σ') → e ⟦ o ⟧ ↦* e' → e ⇝! e' 
--⇝!-complete {e = e} o [] = [] o
--⇝!-complete {e = Z} o (() ∷ r)
--⇝!-complete {e = S e} o (() ∷ r)
--⇝!-complete {e = var x} o (() ∷ r)
--⇝!-complete {e = mvar (x , p)} o (x₁ ∷ r) =  ⊥-elim (↦-NotFromVal x (toValPos p (lookupI₂ x o)) x₁)
--⇝!-complete {e = case Z alt₀ e₁ altₛ e₂} o (x ∷ r) = {!!}
--⇝!-complete {e = case S e alt₀ e₁ altₛ e₂} o (x ∷ r) = {!!}
--⇝!-complete {e = case var x alt₀ e₁ altₛ e₂} o (prom () ∷ r)
--⇝!-complete {e = case mvar x alt₀ e₁ altₛ e₂} o (x₁ ∷ r) = {!!}
--⇝!-complete {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) with ⇝!-complete {e = case e alt₀ e₁ altₛ e₂} o (r ∷ [])
--⇝!-complete {m} {V} {σ} {σ'} {e'} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) | [] o₁ = ⇝!-complete {!!} {!!} -- (↦*-lift {!r*!} {!!})
--⇝!-complete {m} {V} {σ} {σ''} {e''} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) | x ∷ r' = {!!}
          


--   bindZ : (x : Fin m) → (p : Pos (lookup x σ)) → (mvar x p) ⇝⟨ {!!} ⟩⇝ Z
--   bindS : (x : Fin m) → (p : Pos (lookup x σ)) → (mvar x p) ⇝⟨ {!!} ⟩⇝ S (mvar x {!!}) 
--   bindS :                    (mvar x p S) (p +ₚ there here)
  

 
 

