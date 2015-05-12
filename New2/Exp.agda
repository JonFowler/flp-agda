module Exp where

open import Data.Product hiding (zip)
open import Data.Vec as V hiding (_∈_)
open import Data.Fin hiding (_+_ ) hiding (lift) hiding (_≤_)
open import Data.Nat hiding (_≤_)
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
  _∷_ : ∀{e e' e''} → e ↦ e' → e' ↦* e'' → e ↦* e''
  

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


data _⇥_ {m V : ℕ}{σ : Subs m} : Exp V σ → MVar σ → Set where
    susp : (x : MVar σ) → mvar x ⇥ x
    subj-susp : ∀{e e₀ eₛ x} → e ⇥ x → case e alt₀ e₀ altₛ eₛ ⇥ x
    
_[_//_] : ∀{m}(σ : Subs m) → (x : MVar σ) → (s : Sub) → Subs m
(s ∷ σ) [ zero , p // s' ] =  s [ p //ₛ s' ] ∷ σ
(s ∷ σ) [ suc x , p // s' ] = s ∷ σ [ x , p // s' ]
    
_/_ : ∀{m}{σ : Subs m} → (x : MVar σ) → (s : Sub) → σ ≤ σ [ x // s ]
_/_ {σ = s ∷ σ} (zero , p) s' = (p /ₛ s') ∷ ≤-refl
_/_ {σ = s ∷ σ} (suc x , p) s' = ≤ₛ-refl ∷ (x , p) / s'

data _⇝G_ {m V : ℕ}{σ σ' : Subs m} : Exp V σ → Exp V σ' → Set where 
  narr : ∀{e} → (o : σ ≤ σ') → e ⇝G e ⟦ o ⟧

data _⇝N_ {m V : ℕ}{σ : Subs m} : {σ' : Subs m} → Exp V σ → Exp V σ' → Set where 
  narrZ : ∀{e} → (x : MVar σ) →  e ⇥ x → e ⇝N e ⟦ x / Z ⟧
  narrS : ∀{e} → (x : MVar σ) →  e ⇥ x → e ⇝N e ⟦ x / S hole ⟧
  
⇝N-⇝G : {m V : ℕ}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → e ⇝N e' → e ⇝G e'
⇝N-⇝G (narrZ x s) = narr (x / Z)
⇝N-⇝G (narrS x s) = narr (x / S hole)

data _⇝_ {m V : ℕ}{σ : Subs m} : {σ' : Subs m} → Exp V σ → Exp V σ' → Set where 
  narrZ : ∀{e} → (x : MVar σ) →  e ⇥ x → e ⇝ e ⟦ x / Z ⟧
  narrS : ∀{e} → (x : MVar σ) →  e ⇥ x → e ⇝ e ⟦ x / S hole ⟧
  red : ∀{e e'} → e ↦ e' → e ⇝ e'

⇝-mono : ∀{V m}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → e ⇝ e' → σ ≤ σ'
⇝-mono (narrZ x x₁) = x / Z
⇝-mono (narrS x x₁) = x / S hole
⇝-mono (red x) = ≤-refl

data _⇝!_ {m V}{σ : Subs m} : {σ' : Subs m} → Exp V σ → Exp V σ' → Set  where
  [] : ∀{e σ'} → (o : σ ≤ σ') → e ⇝! e ⟦ o ⟧
  _∷_ : ∀{σ' σ'' e}{e' : Exp V σ'}{e'' : Exp V σ''} →  e ⇝ e' → e' ⇝! e'' → e ⇝! e''

⇝!-mono : ∀{V m}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → e ⇝! e' → σ ≤ σ'
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
--
--rep-fromVP : {V' m : ℕ}{σ : Subs m}(V : ℕ) → (e' : Exp V' σ) → (x : Fin m) →  (vp : ValPos (lookup x σ))    →  rep V (fromValPos x vp) e' ≡ fromValPos x vp

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

⇝!-sound : ∀{m V}{σ σ' : Subs m}{e : Exp V σ}{e' : Exp V σ'} → (r : e ⇝! e') → e ⟦ ⇝!-mono r ⟧ ↦* e'
⇝!-sound {e = e} ([] o) = [] 
⇝!-sound {e = e}{e'} (narrZ x s ∷ r) = subst (λ e → e ↦* e') 
            (⟦⟧-func e (x / Z) (⇝!-mono r)) (⇝!-sound r) 
⇝!-sound {e = e}{e'} (narrS x s ∷ r) = subst (λ e → e ↦* e') 
            (⟦⟧-func e (x / S hole) (⇝!-mono r)) (⇝!-sound r)
⇝!-sound (_∷_ {e = e}{e'}{e''} (red r) r*) = let 
      eq1 = sym (cong (λ e → e ⟦ ⇝!-mono r* ⟧) (⟦⟧-refl {e = e} ≤-refl))
      eq2 = ⟦⟧-func e ≤-refl (⇝!-mono r*)
      r' = (↦-lift r (⇝!-mono r*))
      r'' = subst (λ e → e ↦ e' ⟦ ⇝!-mono r* ⟧) (trans eq1 eq2) r'
     in r'' ∷ ⇝!-sound r*
     
↦-NotFromVal : ∀{m V}{σ : Subs m}{e' : Exp V σ} → (x : Fin m) → (vp : ValPos (lookup x σ)) →  ¬ (fromValPos x vp ↦ e')
↦-NotFromVal x (pos p) ()
↦-NotFromVal x Z ()
↦-NotFromVal x (S vp) ()


⇝-complete : ∀{m V}{σ σ' : Subs m}{e' : Exp V σ'}{e : Exp V σ} → (o : σ ≤ σ') → e ⟦ o ⟧ ↦ e' → e ⇝! e' 
⇝-complete {e} o r = {!!}

⇝!-complete : ∀{m V}{σ σ' : Subs m}{e' : Exp V σ'}{e : Exp V σ} → (o : σ ≤ σ') → e ⟦ o ⟧ ↦* e' → e ⇝! e' 
⇝!-complete {e = e} o [] = [] o
⇝!-complete {e = Z} o (() ∷ r)
⇝!-complete {e = S e} o (() ∷ r)
⇝!-complete {e = var x} o (() ∷ r)
⇝!-complete {e = mvar (x , p)} o (x₁ ∷ r) =  ⊥-elim (↦-NotFromVal x (toValPos p (lookupI₂ x o)) x₁)
⇝!-complete {e = case Z alt₀ e₁ altₛ e₂} o (x ∷ r) = {!!}
⇝!-complete {e = case S e alt₀ e₁ altₛ e₂} o (x ∷ r) = {!!}
⇝!-complete {e = case var x alt₀ e₁ altₛ e₂} o (prom () ∷ r)
⇝!-complete {e = case mvar x alt₀ e₁ altₛ e₂} o (x₁ ∷ r) = {!!}
⇝!-complete {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) with ⇝!-complete {e = case e alt₀ e₁ altₛ e₂} o (r ∷ [])
⇝!-complete {m} {V} {σ} {σ'} {e'} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) | [] o₁ = ⇝!-complete {!!} {!!} -- (↦*-lift {!r*!} {!!})
⇝!-complete {m} {V} {σ} {σ''} {e''} {case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o (prom r ∷ r*) | x ∷ r' = {!!}
          


--   bindZ : (x : Fin m) → (p : Pos (lookup x σ)) → (mvar x p) ⇝⟨ {!!} ⟩⇝ Z
--   bindS : (x : Fin m) → (p : Pos (lookup x σ)) → (mvar x p) ⇝⟨ {!!} ⟩⇝ S (mvar x {!!}) 
--   bindS :                    (mvar x p S) (p +ₚ there here)
  

 
 

