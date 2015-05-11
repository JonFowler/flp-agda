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

data Exp {M : ℕ} (V : ℕ) (σ : Subs M) : Set where
  Z : Exp V σ 
  S :  Exp V σ → Exp V σ
  var : Fin V → Exp V σ 
  mvar : (x : Fin M) → (p : Pos (lookup x σ))  → Exp V σ 
  case_alt₀_altₛ_ : Exp V σ → Exp V σ → Exp (suc V) σ → Exp V σ
 
fromValPos : ∀{m V}{σ : Subs m} → (x : Fin m) → ValPos (lookup x σ) → Exp V σ
fromValPos x (pos p) = mvar x p
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
sucExp V (mvar x p) = mvar x p
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

rep : {V' m : ℕ}{σ : Subs m} (V : ℕ) → Exp (V + suc V') σ → Exp V' σ → Exp (V + V') σ
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (mvar x p) ef = mvar x p
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

_⟪_⟫ : {m V : ℕ}{σ : Subs m} → Exp (suc V) σ → Exp V σ → Exp V σ
_⟪_⟫ = rep 0

data _↦_ {m V : ℕ}{σ : Subs m} : Exp V σ → Exp V σ → Set where
  caseZ :  (e₀ : Exp V σ) → (eₛ : Exp (suc V) σ) → case Z alt₀ e₀ altₛ eₛ ↦ e₀
  caseS : (e : Exp V σ) → (e₀ : Exp V σ) → (eₛ : Exp (suc V) σ)   
                → case (S e) alt₀ e₀ altₛ eₛ ↦ eₛ ⟪ e ⟫
  prom : {e e' e₀ : Exp V σ}{eₛ : Exp (suc V) σ} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               

--data Star {A : Set}(P : A → A → Set) : A → A → Set where
--  [] : {e : A} → Star P e e
--  _∷_ : {e e' e'' : A} → P e  e' → Star P e' e'' → Star P e e''
--  
--_↦*_ : {V M : ℕ} → Exp V M → Exp V M → Set
--_↦*_ = Star _↦_

_⇀_ : ∀{m} → Subs m → Subs m → Set
_⇀_ {m} σ σ' = {V : ℕ} → (x : Fin m) → (p : Pos (lookup x σ)) → Exp V σ'

_=<<E_ : ∀{V m}{σ σ' : Subs m} → (f : σ ⇀ σ') → (e : Exp V σ) → Exp V σ' 
_=<<E_ f Z = Z
_=<<E_ f (S e) = S (f =<<E e)
_=<<E_ f (var x) = var x
_=<<E_ f (mvar x p) = f x p
_=<<E_ f (case e alt₀ e₁ altₛ e₂) = case f =<<E e alt₀ f =<<E e₁ altₛ (f =<<E e₂)

returnE : ∀{m}{σ : Subs m} → σ ⇀ σ 
returnE = mvar

=<<E-left : ∀{V m}{σ : Subs m} → (e : Exp V σ) → (returnE =<<E e) ≡ e
=<<E-left Z = refl
=<<E-left (S e) = cong S (=<<E-left e)
=<<E-left (var x) = refl
=<<E-left (mvar x p) = refl
=<<E-left (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<E-left e) (=<<E-left e₁) (=<<E-left e₂)

=<<E-right : ∀{m V}{σ σ' : Subs m} → 
          (f : σ ⇀ σ') 
          → (x : Fin m) → (p : Pos (lookup x σ)) → f =<<E returnE x p ≡ f {V} x p  
=<<E-right f x p = refl

_=<<E-eq_ : ∀{V m}{σ σ' : Subs m} → 
      {f g : σ ⇀ σ'}  →
      ({V' : ℕ}(x : Fin m) → (p : Pos (lookup x σ)) → f {V'} x p ≡ g x p) → 
       (e : Exp V σ) → f =<<E e ≡ g =<<E e 
_=<<E-eq_ f Z = refl
_=<<E-eq_ f (S e) = cong S (f =<<E-eq e)
_=<<E-eq_ f (var x) = refl
_=<<E-eq_ f (mvar x p) = f x p
_=<<E-eq_ f (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (f =<<E-eq e) (f =<<E-eq e₁) (f =<<E-eq e₂)

=<<E-ord : ∀{V m}{σ σ' σ'' : Subs m} (f : σ ⇀ σ') → (g : σ' ⇀ σ'') → (e : Exp V σ) → 
           (g =<<E (f =<<E e)) ≡ (λ x p → g =<<E (f x p)) =<<E e
=<<E-ord f g Z = refl
=<<E-ord f g (S e) = cong S (=<<E-ord f g e)
=<<E-ord f g (var x) = refl
=<<E-ord f g (mvar x p) = refl
=<<E-ord f g (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (=<<E-ord f g e) (=<<E-ord f g e₁) (=<<E-ord f g e₂)

fromValPos-func : ∀{m V}{σ σ' : Subs m} → (x : Fin m) → 
    (f : (x' : Fin m) → Pos (lookup x' σ) → ValPos (lookup x' σ')) →  (vp : ValPos (lookup x σ))
  → (λ x' p → fromValPos x' (f x' p)) =<<E (fromValPos {V = V} x vp) ≡ fromValPos x (f x =<< vp)
fromValPos-func x f (pos p) = refl
fromValPos-func x f Z = refl
fromValPos-func x f (S vp) = cong S (fromValPos-func x f vp)


_⟦_⟧ : ∀{V m}{σ σ' : Subs m} → (e : Exp V σ) → (σ ≤ σ') → Exp V σ' 
e ⟦ σ ⟧ =  (λ x p → fromValPos x (toValPos p (lookupI₂ x σ))) =<<E e 

⟦⟧-refl : ∀{V m}{σ : Subs m} → (e : Exp V σ) → (o : σ ≤ σ) → e ⟦ o ⟧ ≡ e
⟦⟧-refl e o = trans ((λ x p → cong (fromValPos x) (toValPos-refl p (lookupI₂ x o))) =<<E-eq e) 
              (=<<E-left e)

⟦⟧-ord : ∀{V m}{σ σ' σ'' : Subs m} → (e : Exp V σ) → (o : σ ≤ σ') → (o' : σ' ≤ σ'') → 
         e ⟦ o ⟧ ⟦ o' ⟧ ≡ e ⟦ o' ≤-∘ o ⟧
⟦⟧-ord e o o' = 
  trans (=<<E-ord (λ x p → fromValPos x (toValPos p (lookupI₂ x o))) 
                  (λ x p → fromValPos x (toValPos p (lookupI₂ x o'))) e) 
        ((λ x p → trans (fromValPos-func x (λ x' p' → toValPos p' (lookupI₂ x' o'))  (toValPos p (lookupI₂ x o))) 
                         (cong (fromValPos x) (
                  let r = toValPos-ord p (lookupI₂ x o) (lookupI₂ x o') in trans r (cong (toValPos p) (≤ₛ-uniq (lookupI₂ x o' ≤ₛ-∘ lookupI₂ x o) (lookupI₂ x (o' ≤-∘ o))))))) 
                =<<E-eq e) -- {!!} =<<E-eq e
--⟦⟧-ord (mvar x p) o o' = {!!} -- cong (fromValPos x) {!!}


--_⟦ₛ_⟧ : ∀{V} → (e : Exp' V) → (τ : Sub) → Exp' V
--e ⟦ₛ σ ⟧ = mapPos' (λ p → toExp' p σ) e
----Z ⟦ₛ σ ⟧ = Z
----S e ⟦ₛ σ ⟧ = S (e ⟦ₛ σ ⟧)
----var x ⟦ₛ σ ⟧ = var x
----mvar p ⟦ₛ σ ⟧ = toExp' p σ 
----(case e alt₀ e₁ altₛ e₂) ⟦ₛ σ ⟧ = case e ⟦ₛ σ ⟧ alt₀ e₁ ⟦ₛ σ ⟧ altₛ e₂ ⟦ₛ σ ⟧
--
--subs-over : ∀{V} {σ τ : Sub} → σ ≤ₛ τ → (e : Exp' V) → e ⟦ₛ τ ⟧ ≡ (e ⟦ₛ σ ⟧) ⟦ₛ τ ⟧
--subs-over o Z = refl
--subs-over o (S e) = cong S (subs-over o e)
--subs-over o (var x) = refl
--subs-over o (mvar p) = {!!} --  (lookupS-mono p (lookupI₂ x o)) refl 
--subs-over o (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-over o e) (subs-over o e₁) (subs-over o e₂)
--
----conv-there : ∀{V s s'} → (conv' {V = V} s) ⟦ₛ S s' ⟧ ≡ mapPos' there (conv' s ⟦ₛ s' ⟧)
----conv-there {s = hole} = refl
----conv-there {s = Z} = refl
----conv-there {s = S s}{s' = s'} = cong S {!!}
--
--conv-over : ∀{V s s'} → s ≤ₛ s' → (conv' {V} s') ≡ (conv' s) ⟦ₛ s' ⟧
--conv-over ≤ₛ-hole = refl
--conv-over ≤ₛ-Z = refl
--conv-over {s = S s}{s' = S s'} (≤ₛ-S o) = cong (λ x → S x) (trans (trans (cong (mapPos' (λ p → mvar (there p))) (conv-over o)) 
--           (sym (mapPos'-func (λ p → mvar (there p)) (λ p → toExp' p s') (conv' s))))
--          (mapPos'-func (λ p → toExp' p (S s')) (λ p → mvar (there p)) (conv' s)))
--          
----test : mapPos' (λ p → mvar (there p) (e ⟦ₛ s ⟧) ≡ (mapPos' (λ p → mvar (there p)) e) ⟦ₛ S s ⟧  
--
--
--toExp-over : ∀{V}{s s' : Sub}  (p : Pos) → (s ≤ₛ s') → toExp' {V = V} p s'  ≡ toExp' p s ⟦ₛ s' ⟧
--toExp-over here ≤ₛ-hole = refl
--toExp-over (there p) ≤ₛ-hole = refl
--toExp-over here ≤ₛ-Z = refl
--toExp-over (there p) ≤ₛ-Z = refl
--toExp-over here (≤ₛ-S o) = cong S ({!o!})
--toExp-over {V} (there p) (≤ₛ-S o) = let r = toExp-over {V} p o in {!!}



--_⟦_⟧ : ∀{V M}{σ τ : Subs M} → (e : Exp V M) → (σ ≤ τ) → Exp V M
--_⟦_⟧ {τ = τ} e o = e ⟦ₛ τ ⟧
--
--conv-over : ∀{V M} {τ : Subs M}{x : Fin M} {s s' : Sub}  (p : Pos) → (s ≤ₛ s') → s' ≡ lookupS p (lookup x τ) → conv {V = V} x p s' ≡ conv x p s ⟦ₛ τ ⟧
--conv-over {x = x} p ≤ₛ-hole eq = cong (conv x p) eq
--conv-over p ≤ₛ-Z eq = refl
--conv-over p (≤ₛ-S o) eq = cong S (conv-over (there p) o (there-lookupS p eq))
--
--∈-conv : ∀{V M}{σ : Subs M}{x : Fin M}{s : Sub}{p : Pos} → p ∈ₛ s →  s ≡ lookupS p (lookup x σ) → conv {V = V} x p s ∈E σ
--∈-conv {s = hole} here i = mvar (subst (λ x → here ∈ₛ x) i here) 
--∈-conv {s = Z} p i = Z
--∈-conv {s = S s} (there p') i = S (∈-conv {!!} {!!})
----(let eq = there-lookupS p i in ∈-conv {p = there p} (there p') ?)
--

--subs-order : ∀{V M} {σ σ' σ'' : Subs M} → (o : σ ≤ σ') → (o' : σ' ≤ σ'') → 
--             (e : Exp V M) → e ⟦ ≤-trans o o' ⟧ ≡ (e ⟦ o ⟧) ⟦ o' ⟧
--subs-order o o' = subs-over o'
--
--
--∈-subs : ∀{V M}{σ σ' : Subs M}{e : Exp V M} → e ∈E σ → (o : σ ≤ σ') → e ⟦ o ⟧ ∈E σ'
--∈-subs Z o = Z
--∈-subs (S e) o = S (∈-subs e o)
--∈-subs var o = var
--∈-subs (mvar x₁) o = {!!}
--∈-subs (case e₁ alt₀ e₂ altₛ e₃) o = case ∈-subs e₁ o alt₀ ∈-subs e₂ o altₛ ∈-subs e₃ o


 
 

