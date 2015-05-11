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
  
data Exp' (V : ℕ) : Set where
  Z : Exp' V 
  S :  Exp' V  → Exp' V 
  var : Fin V → Exp' V 
  mvar : (p : Pos)  → Exp' V
  case_alt₀_altₛ_ : Exp' V → Exp' V → Exp' (suc V) → Exp' V 
 
data _∈E'_ {V : ℕ} : Exp' V → Sub → Set where
  Z : ∀{σ} → Z ∈E' σ
  S : ∀{e σ} → e ∈E' σ → S e ∈E' σ
  var : ∀{σ}{v : Fin V} → var v ∈E' σ
  mvar : ∀{σ}{p : Pos} → p ∈ₛ σ  → mvar p ∈E' σ
  case_alt₀_altₛ_ : ∀{e e' e'' σ} → e ∈E' σ → e' ∈E' σ → e'' ∈E' σ → case e alt₀ e' altₛ e'' ∈E' σ
  
mapPos' : ∀{V} → (∀{V'} → Pos → Exp' V') → Exp' V → Exp' V
mapPos' f Z = Z
mapPos' f (S e) = S (mapPos' f e)
mapPos' f (var x) = var x
mapPos' f (mvar p) = f p
mapPos' f (case e alt₀ e₁ altₛ e₂) = case mapPos' f e alt₀ mapPos' f e₁ altₛ mapPos' f e₂

mapPos'-func : ∀{V} → (f g : ∀{V'} → Pos → Exp' V') → (e : Exp' V) → mapPos' {V} (λ p → mapPos' f (g p)) e ≡ mapPos' f  (mapPos' g e)
mapPos'-func f g Z = refl
mapPos'-func f g (S e) = cong S (mapPos'-func f g e)
mapPos'-func f g (var x) = refl
mapPos'-func f g (mvar p) = refl
mapPos'-func f g (case e alt₀ e₁ altₛ e₂) = 
  cong₃ case_alt₀_altₛ_ (mapPos'-func f g e) (mapPos'-func f g e₁) (mapPos'-func f g e₂)
  

conv' : ∀{V} → (s : Sub) → Exp' V
conv' hole = mvar here
conv' Z = Z
conv' (S s) = S (mapPos' (λ p → mvar (there p)) (conv' s)) 

∈-conv' : ∀{V} → (s : Sub) → conv' {V} s ∈E' s 
∈-conv' hole = mvar here
∈-conv' Z = Z
∈-conv' (S s) = S {!!}

toExp' : ∀{V} (p : Pos) → (s : Sub) → Exp' V
toExp' (there p) (S s) = mapPos' (λ p → mvar (there p)) (toExp' p s) -- mapPos' (λ p' → p +ₚ p') (conv' (lookupS p s))
toExp' here s = conv' s
toExp' (there p) hole = mvar (there p)
toExp' (there p) Z = mvar (there p)

∈-toExp' : ∀{V}{σ τ : Sub} → (σ ≤ₛ τ) → (p : Pos) 
          → (p ∈ₛ σ) → toExp' {V = V} p τ ∈E' τ
∈-toExp' ≤ₛ-hole here here = {!!}
∈-toExp' ≤ₛ-Z p ()
∈-toExp' (≤ₛ-S o) (there p) (there i) = {!!}


conv : ∀{V M} (x : Fin M) → (p : Pos) → (s : Sub) → Exp V M
conv x p hole = mvar x p
conv x p Z = Z
conv x p (S s) = S (conv x (there p) s)

toExp : ∀{M V} (x : Fin M) → (p : Pos) → (s : Sub) → Exp V M
toExp x p s = conv x p (lookupS p s) 

∈-toExp : ∀{M V}{σ τ : Subs M} → (σ ≤ τ) → (x : Fin M) → (p : Pos) 
          → (p ∈ₛ lookup x σ) → toExp {V = V} x p (lookup x τ) ∈E τ
∈-toExp ((≤ₛ-hole {s = s}) ∷ o) zero here here = {!s!}
∈-toExp (≤ₛ-Z ∷ o) zero p ()
∈-toExp (≤ₛ-S x ∷ o) zero (there p) (there p') = {!∈-toExp (≤ₛ-S x ∷ o) zero p p'!}
∈-toExp o (suc x) p p' = {!!}

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

rep : {V' M : ℕ} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
rep V Z ef = Z
rep V (S x) ef = S (rep V x ef)
rep zero (var zero) ef = ef
rep zero (var (suc x)) ef = var x
rep (suc V) (var zero) ef = var zero
rep (suc V) (var (suc x)) ef with rep V (var x) ef
... | e' = sucExp 0 e'
rep V (mvar x p) ef = mvar x p
rep V (case e alt₀ e₁ altₛ e₂) ef = case rep V e ef alt₀ rep V e₁ ef altₛ rep (suc V) e₂ ef

rep-in : {V' M : ℕ}(V : ℕ){σ : Subs M}{e : Exp (V + suc V') M}{e' : Exp V' M} 
             → e ∈E σ → e' ∈E σ → rep V e e' ∈E σ
rep-in V Z e'' = Z
rep-in V (S e₁) e'' = S (rep-in V e₁ e'')
rep-in zero {e = var zero} var e'' = e''
rep-in zero {e = var (suc v)} var e'' = var 
rep-in (suc V) {e = var zero} var e'' = var
rep-in (suc V) {e = var (suc v)} var e'' with rep-in V {e = var v} var e''
... | b  = sucExp-in 0 b
rep-in V (mvar x₁) e'' = mvar x₁
rep-in V (case e₁ alt₀ e₂ altₛ e₃) e'''' = case rep-in V e₁ e'''' alt₀ rep-in V e₂ e'''' altₛ
                                             rep-in (suc V) e₃ e''''

_⟪_⟫ : {V M : ℕ} → Exp (suc V) M → Exp V M → Exp V M
_⟪_⟫ = rep 0

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

--_⟦ₛ_⟧ : ∀{V M} → (e : Exp V M) → (τ : Subs M) → Exp V M
--Z ⟦ₛ σ ⟧ = Z
--S e ⟦ₛ σ ⟧ = S (e ⟦ₛ σ ⟧)
--var x ⟦ₛ σ ⟧ = var x
--mvar x p ⟦ₛ σ ⟧ = toExp x p (lookup x σ) 
--(case e alt₀ e₁ altₛ e₂) ⟦ₛ σ ⟧ = case e ⟦ₛ σ ⟧ alt₀ e₁ ⟦ₛ σ ⟧ altₛ e₂ ⟦ₛ σ ⟧

_⟦ₛ_⟧ : ∀{V} → (e : Exp' V) → (τ : Sub) → Exp' V
e ⟦ₛ σ ⟧ = mapPos' (λ p → toExp' p σ) e
--Z ⟦ₛ σ ⟧ = Z
--S e ⟦ₛ σ ⟧ = S (e ⟦ₛ σ ⟧)
--var x ⟦ₛ σ ⟧ = var x
--mvar p ⟦ₛ σ ⟧ = toExp' p σ 
--(case e alt₀ e₁ altₛ e₂) ⟦ₛ σ ⟧ = case e ⟦ₛ σ ⟧ alt₀ e₁ ⟦ₛ σ ⟧ altₛ e₂ ⟦ₛ σ ⟧




subs-over : ∀{V} {σ τ : Sub} → σ ≤ₛ τ → (e : Exp' V) → e ⟦ₛ τ ⟧ ≡ (e ⟦ₛ σ ⟧) ⟦ₛ τ ⟧
subs-over o Z = refl
subs-over o (S e) = cong S (subs-over o e)
subs-over o (var x) = refl
subs-over o (mvar p) = {!!} --  (lookupS-mono p (lookupI₂ x o)) refl 
subs-over o (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-over o e) (subs-over o e₁) (subs-over o e₂)

--conv-there : ∀{V s s'} → (conv' {V = V} s) ⟦ₛ S s' ⟧ ≡ mapPos' there (conv' s ⟦ₛ s' ⟧)
--conv-there {s = hole} = refl
--conv-there {s = Z} = refl
--conv-there {s = S s}{s' = s'} = cong S {!!}

conv-over : ∀{V s s'} → s ≤ₛ s' → (conv' {V} s') ≡ (conv' s) ⟦ₛ s' ⟧
conv-over ≤ₛ-hole = refl
conv-over ≤ₛ-Z = refl
conv-over {s = S s}{s' = S s'} (≤ₛ-S o) = cong (λ x → S x) (trans (trans (cong (mapPos' (λ p → mvar (there p))) (conv-over o)) 
           (sym (mapPos'-func (λ p → mvar (there p)) (λ p → toExp' p s') (conv' s))))
          (mapPos'-func (λ p → toExp' p (S s')) (λ p → mvar (there p)) (conv' s)))
          
--test : mapPos' (λ p → mvar (there p) (e ⟦ₛ s ⟧) ≡ (mapPos' (λ p → mvar (there p)) e) ⟦ₛ S s ⟧  


toExp-over : ∀{V}{s s' : Sub}  (p : Pos) → (s ≤ₛ s') → toExp' {V = V} p s'  ≡ toExp' p s ⟦ₛ s' ⟧
toExp-over here ≤ₛ-hole = refl
toExp-over (there p) ≤ₛ-hole = refl
toExp-over here ≤ₛ-Z = refl
toExp-over (there p) ≤ₛ-Z = refl
toExp-over here (≤ₛ-S o) = cong S ({!o!})
toExp-over {V} (there p) (≤ₛ-S o) = let r = toExp-over {V} p o in {!!}



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


 
 

