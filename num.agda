module num where

open import Data.Product hiding (zip)
open import Data.Vec as V
open import Data.Maybe as M
open import Data.Fin hiding (_+_ ) hiding (lift)
open import Data.Nat 
open import Function
open import Data.Unit
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import VecI
open import Sub

data Exp (V : ℕ) (M : ℕ) : Set where
  Z : Exp V M
  S :  Exp V M → Exp V M
  var : Fin V → Exp V M
  mvar : (x : Fin M) → (p : SubVar )  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  
data _∈E_ {V M : ℕ} : Exp V M → Subs M → Set where
  Z : ∀{σ} → Z ∈E σ
  S : ∀{e σ} → e ∈E σ → S e ∈E σ
  var : {v : Fin V}{σ : Subs M} → var v ∈E σ
  mvar : ∀{σ}{x : Fin M}{p : SubVar} → p ∈ₛ lookup x σ  → mvar x p ∈E σ
  case_alt₀_altₛ_ : ∀{e e' e'' σ} → e ∈E σ → e' ∈E σ → e'' ∈E σ → case e alt₀ e' altₛ e'' ∈E σ 
  
Red : Set → Set₁ 
Red A =  A → A → Set
  
∈E-uniq : ∀{V M}{e : Exp V M}{σ : Subs M} → (i1 : e ∈E σ) → (i2 : e ∈E σ) → i1 ≡ i2
∈E-uniq Z Z = refl
∈E-uniq (S i1) (S i2) = cong S (∈E-uniq i1 i2)
∈E-uniq var var = refl
∈E-uniq (mvar x₁) (mvar x₂) = cong mvar (∈ₛ-uniq x₁ x₂)
∈E-uniq (case i1 alt₀ i2 altₛ i3) (case i4 alt₀ i5 altₛ i6) = cong₃ case_alt₀_altₛ_ (∈E-uniq i1 i4) (∈E-uniq i2 i5) (∈E-uniq i3 i6)

emb-s : ∀{M}{p : SubVar}{σ σ' : Subs M} → σ ≤s σ' → (x : Fin M) → p ∈ₛ lookup x σ → p ∈ₛ lookup x σ' 
emb-s (x ∷ o) zero i = emb-var x i
emb-s (x ∷ o) (suc x₁) i = emb-s o x₁ i

emb-exp : ∀{v m}{σ σ' : Subs m}{e : Exp v m} → σ ≤s σ' → e ∈E σ → e ∈E σ'
emb-exp o Z = Z
emb-exp o (S e₁) = S (emb-exp o e₁)
emb-exp o var = var
emb-exp o (mvar {x = x} x₁) = mvar (emb-s o x x₁)
emb-exp o (case e₁ alt₀ e₂ altₛ e₃) = case emb-exp o e₁ alt₀ emb-exp o e₂ altₛ emb-exp o e₃
  
conv : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → Exp V M
conv x p hole = mvar x p
conv x p Z = Z
conv x p (S s) = S (conv x (there p) s)

conv-in : ∀{M V}{σ : Subs M}{x : Fin M}{s' : Sub}{p : SubVar}  →
        (lookup x σ [ p ]:= s' ) → conv {V = V} x p s' ∈E σ
conv-in {s' = hole} i = mvar (look-in i)
conv-in {s' = Z} i = Z
conv-in {s' = S s'} i = S (conv-in (look-S i))

toExp : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → Exp V M
toExp x p s = conv x p (getSub p s) 

toExp-in : ∀{M V}{σ : Subs M}{x : Fin M}{p : SubVar} → (p ∈ₛ lookup x σ) → 
         toExp {V = V} x p (lookup x σ) ∈E σ 
toExp-in i = conv-in (getSub-in i) 

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
sucExp-in V (S e₁) = S (sucExp-in V e₁)
sucExp-in V var = var
sucExp-in V (mvar x₁) = mvar x₁
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

_[-_-] : {V M : ℕ} → Exp (suc V) M → Exp V M → Exp V M
_[-_-] = sub 0
  
data _↦R_ {V M : ℕ} : Red (Exp V M) where
  caseZ :  (e : Exp V M) → (e' : Exp (suc V) M) → case Z alt₀ e altₛ e' ↦R e
  caseS : {ef : Exp V M} → (e : Exp V M) → (e' : Exp (suc V) M)   
                → case (S ef) alt₀ e altₛ e' ↦R e' [- ef -]
                
↦R-in : ∀{V M}{σ : Subs M}{e e' : Exp V M} → e ↦R  e' → e ∈E σ → e' ∈E σ
↦R-in (caseZ e' e'') (case e₁ alt₀ e₂ altₛ e₃) = e₂
↦R-in (caseS e' e'') (case S e₁ alt₀ e₂ altₛ e₃) = sub-in 0 e₃ e₁

data _↦_ {V M : ℕ} : Red (Exp V M) where
  pure : {e e' : Exp V M} → e ↦R e' → e ↦ e' 
  subj : {e e' e₀ : Exp V M}{eₛ : Exp (suc V) M} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ
               
data Star {A : Set}(P : Red A) : Red A where
  [] : {e : A} → Star P e e
  _∷_ : {e e' e'' : A} → P e  e' → Star P e' e'' → Star P e e''
  
_↦*_ : {V M : ℕ} → Red (Exp V M)
_↦*_ = Star _↦_
  
Env : ℕ → ℕ → Set
Env V M = Subs M × Exp V M

data _⇝M_ {V M : ℕ} : Red (Env V M) where
  mvar : {σ : Subs M}{x : Fin M}{p : SubVar} → let s = lookup x σ in  
             (σ , mvar x p) ⇝M (σ , toExp x p s)   --conv x p s')
  bindZ : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
           {p : SubVar} → s [ p ]:= hole → 
          (σ , mvar x p) ⇝M (update x (updateS Z p) σ , Z) 
  bindS : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
    {p : SubVar} → s [ p ]:= hole → 
    (σ , mvar x p) ⇝M (update x (updateS (S hole) p) σ , S (mvar x (there p)))
    

data _⇝R_ {V M : ℕ} : Red (Env V M) where
  lift : {σ : Subs M}{e e' : Exp V M} → e ↦R e' → (σ , e) ⇝R (σ , e')
  meta : {σ σ' : Subs M}{e e' e'' e₀ : Exp V M}{eₛ : Exp (suc V) M} → (σ , e) ⇝M (σ' , e') → 
               case e' alt₀ e₀ altₛ eₛ ↦R e'' → 
               (σ , case e alt₀ e₀ altₛ eₛ) ⇝R (σ' , e'')
               
_⟪_⟫ : ∀{V M} → (e : Exp V M) → (τ : Subs M) → Exp V M
Z ⟪ ns ⟫ = Z
S e ⟪ ns ⟫ = S (e ⟪ ns ⟫)
var x ⟪ ns ⟫ = var x
mvar x p ⟪ ns ⟫ = toExp x p (lookup x ns) 
(case e alt₀ e₁ altₛ e₂) ⟪ ns ⟫ =
      case e ⟪ ns ⟫ alt₀ e₁ ⟪ ns ⟫ altₛ e₂ ⟪ ns ⟫
 
               
data Fill {V M : ℕ}(P : Env V M → Env V M → Set) : Env V M → Env V M → Set where
  fill : {σ σ' τ : Subs M}{e e' : Exp V M} → (o : σ' ≤s τ) → 
       (r : P (σ , e) (σ' , e')) →  Fill P (σ , e) (τ ,  e' ⟪ τ ⟫)

_⇝RF_  : ∀{V M} → Red (Env V M)
_⇝RF_ = Fill _⇝R_

⇝M-mono : ∀{M V}{σ σ' : Subs M}{e e' : Exp V M} →   (σ , e) ⇝M (σ' , e') → σ ≤s σ'
⇝M-mono mvar = ≤s-refl
⇝M-mono (bindZ {x = x} i) = upd-point x (upd-mono i)
⇝M-mono (bindS {x = x} i) = upd-point x (upd-mono i)

⇝R-mono : ∀{V M}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝R (σ' , e') → σ ≤s σ'
⇝R-mono (lift x) = ≤s-refl
⇝R-mono (meta r x) = ⇝M-mono r

⇝M-in : ∀{V M}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝M (σ' , e') → e ∈E σ → e' ∈E σ'
⇝M-in mvar (mvar x₁) = toExp-in x₁ 
⇝M-in (bindZ x₁) x₂ = Z
⇝M-in {σ = σ} (bindS x₁) (mvar {x = x} {p} x₂) =  
  S (mvar (subst (_∈ₛ_ (there p)) (upd-look x (updateS (S hole) p) σ) (look-in (look-S (updS-var x₂))) )) -- (updS-var x₁ x₂)))

⇝R-in : ∀{V M}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝R (σ' , e') → e ∈E σ → e' ∈E σ'
⇝R-in (lift x) i = ↦R-in x i
⇝R-in (meta x x₁) (case i alt₀ i₁ altₛ i₂) =  ↦R-in x₁ (case ⇝M-in x i alt₀ emb-exp (⇝M-mono x) i₁ altₛ emb-exp (⇝M-mono x) i₂)

    
getSub-up : ∀{p s s'} → S s' ≡ getSub p s → s' ≡ getSub (there p) s 
getSub-up {here} {hole} ()
getSub-up {here} {Z} ()
getSub-up {here} {S s'} refl = refl
getSub-up {there p} {hole} ()
getSub-up {there p} {Z} ()
getSub-up {there p} {S s} eq = getSub-up {p}{s} eq
      
conv-subs : ∀{V M} {τ : Subs M}{x : Fin M}(p : SubVar) → (s : Sub) → s ≡ getSub p (lookup x τ) → conv {V = V} x p s ≡ conv {V = V} x p s ⟪ τ ⟫
conv-subs {x = x} p hole eq = cong (conv x p) eq
conv-subs p Z eq = refl
conv-subs p (S s) eq = cong S (conv-subs (there p) s (getSub-up {p} eq))      

subs-idem : ∀{V M} {τ : Subs M} → (e : Exp V M) → e ⟪ τ ⟫ ≡ (e ⟪ τ ⟫) ⟪ τ ⟫
subs-idem Z = refl
subs-idem (S e) = cong S (subs-idem e)
subs-idem (var x) = refl
subs-idem {τ = τ} (mvar x p) = conv-subs p (getSub p (lookup x τ)) refl
subs-idem (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-idem e) (subs-idem e₁) (subs-idem e₂)

conv-over : ∀{V M} {τ : Subs M}{x : Fin M}(p : SubVar) → (s s' : Sub) → (s ≤ₛ s') → s' ≡ getSub p (lookup x τ) → conv {V = V} x p s' ≡ conv {V = V} x p s ⟪ τ ⟫
conv-over {x = x} p hole s' o eq = cong (conv x p) eq
conv-over p Z Z ≤Z eq = refl
conv-over p (S s) (S s') (≤S o) eq = cong S (conv-over (there p) s s' o (getSub-up {p} eq))

subs-over : ∀{V M} {σ τ : Subs M} → σ ≤s τ → (e : Exp V M) → e ⟪ τ ⟫ ≡ (e ⟪ σ ⟫) ⟪ τ ⟫
subs-over o Z = refl
subs-over o (S e) = cong S (subs-over o e)
subs-over o (var x) = refl
subs-over {σ = σ}{τ}  o (mvar x p) = conv-over p (getSub p (lookup x σ)) (getSub p (lookup x τ)) (getSub-mono p (lookupI₂ x o)) refl -- conv-subs p (getSub p (lookup x σ)) ?
subs-over o (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-over o e) (subs-over o e₁) (subs-over o e₂)
      
--sub-eq : ∀{m v}{e : Exp v m}{σ : Subs m} → {i i' : e ∈E σ} →  e ⟪ σ ⟫ ≡ e ⟪ σ ⟫
--sub-eq {i = i} {i'} with ∈E-uniq i i'
--sub-eq | refl = refl

suc-conv :  ∀{V V' M} {x : Fin M} {p : SubVar}(s : Sub) → 
         sucExp {V' = V'} V (conv x p s) ≡ conv x p s 
suc-conv hole = refl
suc-conv Z = refl
suc-conv {V} (S s) = cong S (suc-conv {V} s)

suc-toExp :  ∀{V V' M} {x : Fin M} (p : SubVar)(s : Sub) → 
         sucExp {V' = V'} V (toExp x p s) ≡ toExp x p s 
suc-toExp p s = suc-conv (getSub p s) 

sub-conv : ∀{V V' M}{e : Exp V' M}{x : Fin M}{p : SubVar}(s : Sub) → 
         sub V (conv x p s) e ≡ conv x p s
sub-conv hole = refl
sub-conv Z = refl
sub-conv {V} (S s) = cong S (sub-conv {V} s)

sub-toExp : ∀{V V' M}{e : Exp V' M}{x : Fin M}(p : SubVar)(s : Sub) → 
         sub V (toExp x p s) e ≡ toExp x p s
sub-toExp p s = sub-conv (getSub p s)

--sub-natToExp : ∀{V V' M}{e : Exp V' M}{x : Fin M}{p : SubVar}(s : Sub)(p' : SubVar) → sub V (natToExp' x p s p') e ≡ natToExp' x p s p'
--sub-natToExp hole here = refl
--sub-natToExp hole (there p₁) = refl
--sub-natToExp Z a = refl
--sub-natToExp (S s) here = cong S (sub-natToExp s here) 
--sub-natToExp (S s) (there p₁) = sub-natToExp s p₁
--
sucExp-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : Exp (V + V') M) → sucExp V (e ⟪ σ ⟫) ≡ sucExp V e ⟪ σ ⟫  
sucExp-subs V Z = refl
sucExp-subs V (S i) = cong S (sucExp-subs V i)
sucExp-subs V (var v) = refl
sucExp-subs V {σ = σ} (mvar x p) = suc-toExp p (lookup x σ)
sucExp-subs V (case i alt₀ i₁ altₛ i₂) = cong₃ case_alt₀_altₛ_ (sucExp-subs V i) (sucExp-subs V i₁) (sucExp-subs (suc V) i₂)
      
sub-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : Exp (V + suc V') M) → (e' : Exp V' M) → sub V (e ⟪ σ ⟫) (e' ⟪ σ ⟫) ≡ sub V e e' ⟪ σ ⟫  
sub-subs V Z i' = refl
sub-subs V (S i) i' = cong S (sub-subs V i i')
sub-subs zero (var zero) i' = refl
sub-subs zero (var (suc v)) i' = refl
sub-subs (suc V) (var (zero)) i' = refl
sub-subs (suc V) (var (suc v)) i' with sub-subs V (var v) i' 
... | p = trans (cong (sucExp 0) p) (sucExp-subs zero (sub V (var v) i')) -- cong (sucExp 0) p
sub-subs V {σ = σ} (mvar x p) i' = sub-toExp p (lookup x σ) -- sub-natToExp (lookup x σ) p
sub-subs V (case i alt₀ i₁ altₛ i₂) i' = cong₃ case_alt₀_altₛ_ (sub-subs V i i') (sub-subs V i₁ i') (sub-subs (suc V) i₂ i')
--     
↦R-subs : ∀{M V}{e e' : Exp V M} → (r : e ↦R e') → (σ : Subs M) →  e ⟪ σ ⟫ ↦R e' ⟪ σ ⟫
↦R-subs (caseZ e e') σ = caseZ (e ⟪ σ ⟫) (e' ⟪ σ ⟫)
↦R-subs (caseS {ef = ef} e e'') σ  = subst (λ e' → (case S (ef ⟪ σ ⟫) alt₀ e ⟪ σ ⟫ altₛ (e'' ⟪ σ ⟫)) ↦R e' ) (sub-subs 0 e'' ef) (caseS (e ⟪ σ ⟫) (e'' ⟪ σ ⟫)) -- caseS ? {!caseS!}


↦R-over : ∀{V M}{e e' : Exp V M}{σ σ' : Subs M} → 
        (σ ≤s σ') → (e ⟪ σ ⟫ ↦R e' ⟪ σ ⟫ )  →  e ⟪ σ' ⟫ ↦R e' ⟪ σ' ⟫
↦R-over {e = e}{e'}{σ}{σ'} o r = subst₂ (λ x x₁ → x ↦R x₁) 
        (sym (subs-over o e)) (sym (subs-over o e')) (↦R-subs r σ')
        
        
↦-subs : ∀{V M}{e e' : Exp V M} → (r : e ↦ e') → (σ : Subs M) →  e ⟪ σ ⟫ ↦ e' ⟪ σ ⟫
↦-subs (pure x) σ = pure (↦R-subs x σ)
↦-subs (subj r) σ = subj (↦-subs r σ)

↦-over : ∀{V M}{e e' : Exp V M}{σ σ' : Subs M} → 
        (σ ≤s σ') → (e ⟪ σ ⟫ ↦ e' ⟪ σ ⟫ )  →  e ⟪ σ' ⟫ ↦ e' ⟪ σ' ⟫
↦-over {e = e}{e'}{σ}{σ'} o r = subst₂ (λ x x₁ → x ↦ x₁) 
        (sym (subs-over o e)) (sym (subs-over o e')) (↦-subs r σ')

↦*-subs : ∀{V M}{e e' : Exp V M} → (r : e ↦* e') → (σ : Subs M) →  e ⟪ σ ⟫ ↦* e' ⟪ σ ⟫
↦*-subs [] σ = []
↦*-subs (x ∷ r) σ = (↦-subs x σ) ∷ ↦*-subs r σ

↦*-over : ∀{V M}{e e' : Exp V M}{σ σ' : Subs M} → 
        (σ ≤s σ') → (e ⟪ σ ⟫ ↦* e' ⟪ σ ⟫ )  →  e ⟪ σ' ⟫ ↦* e' ⟪ σ' ⟫
↦*-over {e = e}{e'}{σ}{σ'} o r = subst₂ (λ x x₁ → x ↦* x₁) 
        (sym (subs-over o e)) (sym (subs-over o e')) (↦*-subs r σ')


--
----case S ? alt₀ e ⟪ σ , i₁ ⟫ altₛ (e'' ⟪ σ , i₂ ⟫)) ↦ e'
--
--lookupZ : ∀{m v}{s : Sub}{p p' : SubVar}{x : Fin m} →  s [ p' ]:= just Z → 
--              Z ≡ natToExp' {V = v} x p s p'
--lookupZ hereZ = refl
--lookupZ (thereZ x₁) = lookupZ x₁
--
--lookupS : ∀{m v}{s : Sub}{p p' : SubVar}{x : Fin m} →  s [ p' ]:= just (S unit) → 
--             (S (natToExp' {V = v} x (there p) (s) here)) ≡ natToExp' {V = v} x p s p'
--lookupS hereS = {!!}
--lookupS (thereS x₁) = {!!} 

Sound : (V M : ℕ) → Red (Env V M) → Red (Exp V M) → Set
Sound V M P Q =  {σ τ : Subs M}{e e' : Exp V M} → 
                    (i : e ∈E σ) → P (σ , e) (τ , e') → Q (e ⟪ τ ⟫ ) e'
                    
Complete : (V M : ℕ) → Red (Env V M) → Red (Exp V M) → Set
Complete V M P Q = {σ τ : Subs M}{e e' es es' : Exp V M} →  (σ ≤s τ) →
                    (i : e ∈E σ) → Q (e ⟪ τ ⟫) e' → P (σ , e) (τ , e')
                    
Correct : (V M : ℕ) → Red (Env V M) → Red (Exp V M) → Set
Correct V M P Q  = (Sound V M P Q) × (Complete V M P Q)

toExp-upd : ∀{p s s' M V}{x : Fin M} → (p ∈ₛ s') →  conv {V = V} x p s ≡ toExp x p (updateS s p s')
toExp-upd {p}{x = x} i = cong (conv x p) (getSub-upd i)

alt₀-eq : ∀{V M}{e e' e1 e1' : Exp V M}{e'' e1'' : Exp (suc V) M} → 
        _≡_ {A = Exp V M} (case e alt₀ e' altₛ e'') (case e1 alt₀ e1' altₛ e1'') → e' ≡ e1'
alt₀-eq refl = refl

altₛ-eq : ∀{V M}{e e' e1 e1' : Exp V M}{e'' e1'' : Exp (suc V) M} → 
        _≡_ {A = Exp V M} (case e alt₀ e' altₛ e'') (case e1 alt₀ e1' altₛ e1'') → e'' ≡ e1''
altₛ-eq refl = refl

subj-eq : ∀{V M}{e e' e1 e1' : Exp V M}{e'' e1'' : Exp (suc V) M} → 
        _≡_ {A = Exp V M} (case e alt₀ e' altₛ e'') (case e1 alt₀ e1' altₛ e1'') → e ≡ e1
subj-eq refl = refl

⇝RF-complete : ∀{V M} → Complete V M (_⇝RF_) (_↦R_)
⇝RF-complete {e = Z} o i ()
⇝RF-complete {e = S e} o i ()
⇝RF-complete {e = var x} o i ()
⇝RF-complete {τ = τ}{e = mvar x p} o i r with getSub p (lookup x τ)
⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () | hole
⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () | Z
⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () | S b
⇝RF-complete {e = case Z alt₀ e₁ altₛ e₂}  o i (caseZ ._ ._) = 
  fill o (lift (caseZ e₁ e₂))
⇝RF-complete {σ = σ}{τ} {e = case S e alt₀ e₁ altₛ e₂} o i (caseS ._ ._) = 
  let r = (caseS {ef = e} e₁ e₂) 
      eq = cong (λ x → τ , x) (sym (sub-subs zero e₂ e))   
  in subst (λ x →  (σ , case S e alt₀ e₁ altₛ e₂) ⇝RF x) eq (fill {e' = e₂ [- e -]} o (lift r))
--  fill o (lift {!caseS!})
⇝RF-complete {e = case var x alt₀ e₁ altₛ e₂} o i ()
⇝RF-complete {σ = σ}{τ}{case mvar x p alt₀ e₁ altₛ e₂} o i r with getSub p (lookup x τ) | inspect (getSub p) (lookup x τ) | getSub p (lookup x σ) | inspect (getSub p) (lookup x σ) | getSub-mono p (lookupI₂ x o)
⇝RF-complete {V} {M} {σ} {τ} {case mvar x p alt₀ e₁ altₛ e₂} o i () | hole | eq | .hole | eq' | ≤hole
⇝RF-complete {V} {M} {σ} {τ} {case mvar x p alt₀ e₁ altₛ e₂} o i (caseZ .(e₁ ⟪ τ ⟫) .(e₂ ⟪ τ ⟫)) | Z | eq | .hole | Reveal_is_.[ eq' ] | ≤hole = {!!}
⇝RF-complete {V} {M} {σ} {τ} {case mvar x p alt₀ e₁ altₛ e₂} o i (caseS .(e₁ ⟪ τ ⟫) .(e₂ ⟪ τ ⟫)) | S s | eq | .hole | eq' | ≤hole = {!!}
⇝RF-complete {V} {M} {σ} {τ} {case mvar x p alt₀ e₁ altₛ e₂} o i (caseZ .(e₁ ⟪ τ ⟫) .(e₂ ⟪ τ ⟫)) | .Z | eq | .Z | Reveal_is_.[ eq' ] | ≤Z = 
  let r = meta (mvar {σ = σ}{x = x}{p = p}) (subst (λ x₁ → case x₁ alt₀ e₁ altₛ e₂ ↦R e₁) (sym (cong (conv x p) eq')) (caseZ e₁ e₂))
  in fill o r
⇝RF-complete {V} {M} {σ} {τ} {case mvar x p alt₀ e₁ altₛ e₂} o i (caseS .(e₁ ⟪ τ ⟫) .(e₂ ⟪ τ ⟫)) | S s' | Reveal_is_.[ eq ] | S s'' | Reveal_is_.[ eq' ] | ≤S o' = 
  let ef = conv x (there p) s'' 
      r  =  (caseS {ef = ef} e₁ e₂)
      r' = meta (mvar {σ = σ}{x = x}{p = p}) (subst (λ x₁ → case x₁ alt₀ e₁ altₛ e₂ ↦R e₂ [- ef -]) (sym (cong (conv x p) eq')) r)
      r'' = fill {P = _⇝R_} {e' = e₂ [- ef -]} o r'
      eq' =  sym (conv-over (there p) s'' s' o' (getSub-there {p = p} (sym eq)))
  in subst (λ x₁ →  (σ , case mvar x p alt₀ e₁ altₛ e₂) ⇝RF (τ , x₁)) (trans (sym (sub-subs zero e₂ ef)) (cong (sub 0 (e₂ ⟪ τ ⟫)) eq')) r'' 
⇝RF-complete {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o i ()

--⇝RF-complete {e = Z} o i () eq2 (caseZ e₁ e'')
--⇝RF-complete {e = S e} o i () eq2 (caseZ e₁ e'')
--⇝RF-complete {e = var x} o i () eq2 (caseZ e₁ e'')
--⇝RF-complete {τ = τ} {e = mvar x p} o i eq1 eq2 (caseZ e₁ e'') with getSub p (lookup x τ)
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseZ e₁ e'') | hole
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseZ e₁ e'') | Z
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseZ e₁ e'') | S b
--⇝RF-complete {e = case Z alt₀ e₁ altₛ e₂} {e' = e'} o i eq1 eq2 (caseZ e₃ e'') =  {!!} -- fill {e' = e'} o (lift {!!})
--  --   fill o  (lift (subst (λ z → case Z alt₀ e₁ altₛ e₂ ↦R z) {!!} (caseZ e₁ e₂)))
--⇝RF-complete {e = case S e alt₀ e₁ altₛ e₂} o i () eq2 (caseZ e₃ e'')
--⇝RF-complete {e = case var x alt₀ e₁ altₛ e₂} o i () eq2 (caseZ e₃ e'')
--⇝RF-complete {e = case mvar x p alt₀ e₁ altₛ e₂} o i eq1 eq2 (caseZ e₃ e'') = {!!}
--⇝RF-complete {e = case case e alt₀ e₁ altₛ e₂ alt₀ e₃ altₛ e₄} o i () eq2 (caseZ e₅ e'')
--⇝RF-complete {e = Z} o i () eq2 (caseS e₁ e'')
--⇝RF-complete {e = S e} o i () eq2 (caseS e₁ e'')
--⇝RF-complete {e = var x} o i () eq2 (caseS e₁ e'')
--⇝RF-complete {τ = τ} {e = mvar x p} o i eq1 eq2 (caseS e₁ e'') with getSub p (lookup x τ)
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseS e₁ e'') | hole
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseS e₁ e'') | Z
--⇝RF-complete {V} {M} {σ} {τ} {mvar x p} o i () eq2 (caseS e₁ e'') | S b
--⇝RF-complete {e = case e alt₀ e₁ altₛ e₂} o i eq1 eq2 (caseS e₃ e'') = {!!}

--⇝R-sound : ∀{V M} → Sound V M (_⇝R_) (_↦R_)
--⇝R-sound {σ = σ} i (lift x) = ↦R-subs x σ
--⇝R-sound {σ = σ} (case (mvar{x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta mvar x') 
--     with getSub p (lookup x σ) | inspect (getSub p) (lookup x σ)
--⇝R-sound {σ = σ} (case mvar x₁ alt₀ i₁ altₛ i₂) (meta mvar ()) | hole | eq 
--⇝R-sound {σ = σ} (case mvar x₁ alt₀ i₁ altₛ i₂) (meta mvar (caseZ e e')) | Z | eq = caseZ (e ⟪ σ ⟫) (e' ⟪ σ ⟫)
--⇝R-sound {σ = σ} (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta mvar (caseS e e'')) | S s | [ eq ]
--   = let ef = conv x (there p) s
--         r = caseS {ef = ef} (e ⟪ σ ⟫) (e'' ⟪ σ ⟫) 
--         eq1 = cong (sub 0 (e'' ⟪ σ ⟫)) (conv-subs (there p) s (getSub-up {p}{lookup x σ} (sym eq))) 
--         eq2 = sub-subs 0 {σ = σ} e'' ef in 
--       subst (λ x₂ → case (S ef) alt₀ e ⟪ σ ⟫ altₛ e'' ⟪ σ ⟫ ↦R x₂) 
--           (trans eq1 eq2 ) r
--⇝R-sound {σ = σ} (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta (bind0 x₂) (caseZ e' e'')) = 
--   let τ = update x (updateS Z p) σ 
--       r = caseZ (e' ⟪ τ ⟫) (e'' ⟪ τ ⟫)
--   in subst (λ x₂ → case x₂ alt₀ e' ⟪ τ ⟫ altₛ e'' ⟪ τ ⟫ ↦R e' ⟪ τ ⟫) 
--               (trans (toExp-upd x₁) (cong (toExp x p) (upd-look x (updateS Z p) σ))) r
--⇝R-sound {σ = σ} (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta (bindS x₂) (caseS e e'')) = 
--   let τ = update x (updateS (S hole) p) σ 
--       r = caseS {ef = mvar x (there p)} (e ⟪ τ ⟫) (e'' ⟪ τ ⟫)
--       eq1 = toExp-upd x₁
--       eq2 = cong (toExp x p) (upd-look x (updateS (S hole) p) σ)
--       eq1'' = cong (toExp x (there p)) (upd-look x (updateS (S hole) p) σ)
--       eq1' = cong (sub zero (e'' ⟪ τ ⟫)) 
--              (trans (cong (conv x (there p)) (getSub-there {p} (getSub-upd x₁))) eq1'') 
--       eq2' = sub-subs zero e'' (mvar x (there p))
--   in subst₂ (λ es er → case es alt₀ e ⟪ τ ⟫ altₛ e'' ⟪ τ ⟫ ↦R er) 
--                (trans eq1 eq2) (trans eq1' eq2') r 
                

--getOrd : ∀{m}{σ σ' : Subs m} → σ ≤s σ' → (x : Fin m) → lookup x σ ≤N lookup x σ'
--getOrd (x ∷ o) zero = x
--getOrd (_ ∷ o) (suc x) = getOrd o x
--
--
----embCxt : ∀{m V}{M N : Subs m} → Cxt V M → M ≤s N → Exp V N → Exp V N
----embCxt hole o e = e
----embCxt (case H alt₀ e' altₛ e'') o e = case (embCxt H o e) alt₀ (embExp o e') altₛ embExp o e''
----
----repl : ∀{V m}(τ : Subs m) → (VecI Nohole τ) → Exp V τ →  Exp V
----repl τ is (nat Z) = nat Z
----repl τ is (nat (S e)) = nat (S (repl τ is e))
----repl τ is (var x) = var x
----repl (a ∷ τ) (x ∷ is) (mvar zero p) = natToExp (a , x) p
----repl (a ∷ τ) (x ∷ is) (mvar (suc x₁) p) = repl τ is (mvar x₁ p)
----repl τ is (case e alt₀ e₁ altₛ e₂) = case repl τ is e alt₀ repl τ is e₁ altₛ repl τ is e₂
--
--
data _⇝_ {V M : ℕ} : Env V M → Env V M → Set where
  pure : {σ σ' : Subs M}{e e' : Exp V M} → (r : (σ , e) ⇝R (σ' , e')) →
             (σ , e) ⇝ (σ' , e')
  subj : {σ σ' : Subs M}{e e' e₀ : Exp V M}{eₛ : Exp (suc V) M} → 
         (r : (σ , e) ⇝ (σ' , e')) → 
           (σ , case e alt₀ e₀ altₛ eₛ) ⇝ (σ' , case e' alt₀ e₀ altₛ eₛ)
           
∈E-subj : ∀{V M}{e e' : Exp V M}{e'' : Exp (suc V) M}{σ : Subs M} → case e alt₀ e' altₛ e'' ∈E σ → e ∈E σ
∈E-subj (case i alt₀ i₁ altₛ i₂) = i

--_⟪cxt|_⟫ : ∀{V M} → Cxt V M → Subs M → Cxt V M
--hole ⟪cxt| σ ⟫ = hole
--(case H alt₀ x altₛ x₁) ⟪cxt| σ ⟫ = case H ⟪cxt| σ ⟫ alt₀ x ⟪ σ ⟫ altₛ x₁ ⟪ σ ⟫
--
--cxt-sub :  ∀{V M}{e : Exp V M}{σ : Subs M} → (H : Cxt V M) →  
--        H [/ e ] ⟪ σ ⟫ ≡ H ⟪cxt| σ ⟫ [/ e ⟪ σ ⟫ ]
--cxt-sub hole = refl
--cxt-sub {σ = σ} (case H alt₀ x altₛ x₁) = cong (λ h → case h alt₀ x ⟪ σ ⟫ altₛ x₁ ⟪ σ ⟫) (cxt-sub H)
           

--⇝-red :  ∀{m}{σ σ' : Subs m}{e e' : Exp 0 m} → 
--         (σ , H [/ e ]) ⇝ (σ' , H [/ e' ]) → (σ , e) ⇝R (σ' , e')
--⇝-red {e = e}{H = hole} r = {!e!}
--⇝-red {H = case H alt₀ x altₛ x₁} r = {!!}
           

--⇝-sound : ∀{V M} → Sound V M (_⇝_) (_↦_)
--⇝-sound i (pure r) = pure (⇝R-sound i r)
--⇝-sound (case i alt₀ i₁ altₛ i₂) (subj r) = subj (⇝-sound i r)

           
⇝-mono : ∀{M V}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝ (σ' , e') → σ ≤s σ'
⇝-mono (pure r) = ⇝R-mono r
⇝-mono (subj r) = ⇝-mono r

⇝-in : ∀{V M}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝ (σ' , e') → e ∈E σ → e' ∈E σ'
⇝-in (pure r) x = ⇝R-in r x
⇝-in (subj r) (case x alt₀ x₁ altₛ x₂) = 
     case ⇝-in r x alt₀ emb-exp (⇝-mono r) x₁ altₛ emb-exp (⇝-mono r) x₂
--
data _⇝*_ {V M : ℕ} : Red (Env V M) where
  [] : {s : Env V M} → s ⇝* s
  _∷_ : {σ σ' σ'' : Subs M}{e e' e'' : Exp V M} → (r : (σ , e) ⇝ (σ' , e')) → (rs : (σ' , e') ⇝* (σ'' , e'')) → (σ , e) ⇝* (σ'' , e'')
  
 
⇝*-mono : ∀{V M}{σ σ' : Subs M}{e e' : Exp V M} → (σ , e) ⇝* (σ' , e') → σ ≤s σ'
⇝*-mono [] = ≤s-refl
⇝*-mono (r ∷ rs) = ≤s-trans (⇝-mono r) (⇝*-mono rs)
  
--⇝*-sound :  ∀{V M} → Sound V M (_⇝*_) (_↦*_)
--⇝*-sound i [] = []
--⇝*-sound {τ = τ} i (_∷_ {σ = σ}{σ'}{.τ}{e}{e'}{e''} r r₁) =  
--  ↦-over {e = e}{e' = e'} (⇝*-mono r₁) (⇝-sound i r) ∷ ⇝*-sound (⇝-in r i) r₁
  
  
 
--⇝*-in : ∀{m}{σ σ' : Subs m}{e e' : Exp 0 m} → (σ , e) ⇝* (σ' , e') → e ∈E σ → e' ∈E σ'
--⇝*-in [] o = o
--⇝*-in (r ∷ r₁) o = ⇝*-in r₁ (⇝-in r o)

_⇝!_ : ∀{V M : ℕ} → Env V M → Env V M → Set
_⇝!_ = Fill _⇝*_ 

--⇝!-sound :  ∀{V M} → Sound V M _⇝!_ (_↦*_)
--⇝!-sound i (fill {τ = τ} {e = e}{e'} o r) =  let r' = ↦*-over {e = e}{e' = e'} o (⇝*-sound i r)
--  in  subst (λ x → (e ⟪ τ ⟫) ↦* x) (subs-idem e') r'


       
--inp! : ∀{m}{τ : Subs m} {e : Exp 0 m}{s : Env m} → s ⇝! (τ , e) → VecI Nohole τ
--inp! {s = proj₁ , proj₂} (fill x o x₁) = x
--






--⇝!-mono : ∀{m}{σ τ : Subs m}{e e' : Exp 0 m} → (σ , e) ⇝! (τ , e') → σ ≤s τ
--⇝!-mono (fill x o r) = ≤s-trans (⇝*-mono r) o 
--
--⇝!-in : ∀{m}{σ τ : Subs m}{e e' : Exp 0 m} → (σ , e) ⇝! (τ , e') → e ∈E σ → e' ∈E τ
--⇝!-in (fill x o r) i = emb-exp o (⇝*-in r i)
--
--⇝*-sound :  ∀{M}{σ τ : Subs M}{e e' : Exp 0 M} → 
--                    (i : e ∈E σ) → (r : (σ , e) ⇝* (τ , e')) →  
--            (e ⟪ τ , emb-exp (⇝*-mono r) i ⟫ ) ↦* (e' ⟪ τ , ⇝*-in r i ⟫ )
--⇝*-sound i [] = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (lift x) H) r₁) = {!i!} -- {!!} ∷ {!⇝*-sound i r₁!}
--⇝*-sound i (_∷_ {s' = ._ , .(H [/ Z ])} (prom (varZ x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (varS x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , .(H [/ Z ])} (prom (bind0 x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (bindS x₁) H) r₁) = {!!}


--⇝!-sound : ∀{M}{σ τ : Subs M}{e e' : Exp 0 M} → 
--                    (i : e ∈E σ) → (r : (σ , e) ⇝! (τ , e')) →  
--            (e ⟪ τ , inp! r , emb-exp (⇝!-mono r) i ⟫) ↦* (e' ⟪ τ , inp! r , ⇝!-in r i ⟫)
--⇝!-sound {τ = τ} {e} i (fill x o []) = subst (λ o' → e ⟪ τ , x , emb-exp o' i ⟫ ↦* e ⟪ τ , x , emb-exp o i ⟫) ≤s-trans-refl []
--⇝!-sound i (fill x o (_∷_ {s' = σ' , ._} (prom r H) r₁)) = {!r!} 
