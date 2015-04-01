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

data ExpM (V : ℕ) (M : ℕ) : Set where
  Z : ExpM V M
  S :  ExpM V M → ExpM V M
  var : Fin V → ExpM V M
  mvar : (x : Fin M) → (p : SubVar )  → ExpM V M 
  case_alt₀_altₛ_ : ExpM V M → ExpM V M → ExpM (suc V) M → ExpM V M
  
data _∈E_ {V M : ℕ} : ExpM V M → Subs M → Set where
  Z : ∀{σ} → Z ∈E σ
  S : ∀{e σ} → e ∈E σ → S e ∈E σ
  var : {v : Fin V}{σ : Subs M} → var v ∈E σ
  mvar : ∀{σ}{x : Fin M}{p : SubVar} → p ∈ₛ lookup x σ  → mvar x p ∈E σ
  case_alt₀_altₛ_ : ∀{e e' e'' σ} → e ∈E σ → e' ∈E σ → e'' ∈E σ → case e alt₀ e' altₛ e'' ∈E σ 
  
∈E-uniq : ∀{V M}{e : ExpM V M}{σ : Subs M} → (i1 : e ∈E σ) → (i2 : e ∈E σ) → i1 ≡ i2
∈E-uniq Z Z = refl
∈E-uniq (S i1) (S i2) = cong S (∈E-uniq i1 i2)
∈E-uniq var var = refl
∈E-uniq (mvar x₁) (mvar x₂) = cong mvar (∈ₛ-uniq x₁ x₂)
∈E-uniq (case i1 alt₀ i2 altₛ i3) (case i4 alt₀ i5 altₛ i6) = cong₃ case_alt₀_altₛ_ (∈E-uniq i1 i4) (∈E-uniq i2 i5) (∈E-uniq i3 i6)

emb-s : ∀{M}{p : SubVar}{σ σ' : Subs M} → σ ≤s σ' → (x : Fin M) → p ∈ₛ lookup x σ → p ∈ₛ lookup x σ' 
emb-s (x ∷ o) zero i = emb-var x i
emb-s (x ∷ o) (suc x₁) i = emb-s o x₁ i

emb-exp : ∀{v m}{σ σ' : Subs m}{e : ExpM v m} → σ ≤s σ' → e ∈E σ → e ∈E σ'
emb-exp o Z = Z
emb-exp o (S e₁) = S (emb-exp o e₁)
emb-exp o var = var
emb-exp o (mvar {x = x} x₁) = mvar (emb-s o x x₁)
emb-exp o (case e₁ alt₀ e₂ altₛ e₃) = case emb-exp o e₁ alt₀ emb-exp o e₂ altₛ emb-exp o e₃
  
Exp : (V : ℕ) → Set
Exp V = ExpM V 0 

getSub : (p : SubVar) → (s : Sub) → Sub
getSub here s = s
getSub (there p) hole = Z
getSub (there p) Z = Z
getSub (there p) (S s) = getSub p s

getSub-in : ∀{p s} → (p ∈ₛ s) → s [ p ]:= getSub p s
getSub-in here = here
getSub-in (there i) = there (getSub-in i)

conv : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → ExpM V M
conv x p hole = mvar x p
conv x p Z = Z
conv x p (S s) = S (conv x (there p) s)

conv-in : ∀{M V}{σ : Subs M}{x : Fin M}{p : SubVar} → let s = lookup x σ in
        (p ∈ₛ s) → conv {V = V} x p s ∈E σ
conv-in {σ = σ}{x} i with lookup x σ
conv-in here | hole = mvar here
conv-in here | Z = Z
conv-in i | S b = S {!!}

  
subToExp : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → 
            (p' : SubVar) →  ExpM V M
subToExp x p hole here = mvar x p
subToExp x p hole (there w) = Z
subToExp x p Z _ = Z
subToExp x p (S s) here = S (subToExp x (there p) s here)
subToExp x p (S s) (there p₁) = subToExp x p s p₁  



subToExp-in : ∀{M V}{σ : Subs M}{x : Fin M}{p : SubVar} → (p ∈ₛ lookup x σ) → (s : Sub) → 
            (p' : SubVar) → subToExp {V = V} x p s p' ∈E σ
subToExp-in i hole here = mvar i
subToExp-in i hole (there p') = Z
subToExp-in i Z p' = Z
subToExp-in i (S s) here = S (subToExp-in {!!} s here)
subToExp-in i (S s) (there p') = subToExp-in i s p'

toExp : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → ExpM V M
toExp x p s = conv x p (getSub p s) 

sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)

sucExp : {V' M : ℕ}(V : ℕ) → ExpM (V + V') M → ExpM (V + suc V') M
sucExp V Z = Z
sucExp V (S x) = S (sucExp V x)
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x p) = mvar x p
sucExp V (case e alt₀ e₁ altₛ e₂) = case (sucExp V e) alt₀ (sucExp V e₁) altₛ sucExp (suc V) e₂

sucExp-in : {V' M : ℕ}(V : ℕ){σ : Subs M}{e : ExpM (V + V') M} 
             → e ∈E σ → sucExp V e ∈E σ
sucExp-in V Z = Z
sucExp-in V (S e₁) = S (sucExp-in V e₁)
sucExp-in V var = var
sucExp-in V (mvar x₁) = mvar x₁
sucExp-in V (case e₁ alt₀ e₂ altₛ e₃) = case sucExp-in V e₁ alt₀ sucExp-in V e₂ altₛ sucExp-in (suc V) e₃

sub : {V' M : ℕ} (V : ℕ) → ExpM (V + suc V') M → ExpM V' M → ExpM (V + V') M
sub V Z ef = Z
sub V (S x) ef = S (sub V x ef)
sub zero (var zero) ef = ef
sub zero (var (suc x)) ef = var x
sub (suc V) (var zero) ef = var zero
sub (suc V) (var (suc x)) ef with sub V (var x) ef
... | e' = sucExp 0 e'
sub V (mvar x p) ef = mvar x p
sub V (case e alt₀ e₁ altₛ e₂) ef = case sub V e ef alt₀ sub V e₁ ef altₛ sub (suc V) e₂ ef

sub-in : {V' M : ℕ}(V : ℕ){σ : Subs M}{e : ExpM (V + suc V') M}{e' : ExpM V' M} 
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

_[-_-] : {V M : ℕ} → ExpM (suc V) M → ExpM V M → ExpM V M
_[-_-] = sub 0
  
data _↦R_ {M : ℕ} : ExpM 0 M → ExpM 0 M → Set where
  caseZ :  (e : ExpM 0 M) → (e' : ExpM 1 M) → case Z alt₀ e altₛ e' ↦R e
  caseS : {ef : ExpM 0 M} → (e : ExpM 0 M) → (e' : ExpM 1 M)   
                → case (S ef) alt₀ e altₛ e' ↦R e' [- ef -]
                
↦R-in : ∀{M}{σ : Subs M}{e e' : ExpM 0 M} → e ↦R  e' → e ∈E σ → e' ∈E σ
↦R-in (caseZ e' e'') (case e₁ alt₀ e₂ altₛ e₃) = e₂
↦R-in (caseS e' e'') (case S e₁ alt₀ e₂ altₛ e₃) = sub-in 0 e₃ e₁

data Cxt (V : ℕ) (M : ℕ)  : Set where
  hole : Cxt V M
  case_alt₀_altₛ_ : Cxt V M → ExpM V M → ExpM (suc V) M → Cxt V M
  
_[/_] : ∀{M V} → Cxt V M → ExpM V M → ExpM V M
hole [/ e ] = e
(case H alt₀ x altₛ x₁) [/ e ] = case H [/ e ] alt₀ x altₛ x₁
  
data _↦_ {M : ℕ} : ExpM 0 M → ExpM 0 M → Set where
  prom : {e e' : ExpM 0 M} → e ↦ e' → (H : Cxt 0 M)  → H [/ e ] ↦ H [/ e' ]

data _↦*_ {M : ℕ} : ExpM 0 M → ExpM 0 M → Set where
  [] : {e : ExpM 0 M} → e ↦* e
  _∷_ : {e e' e'' : ExpM 0 M} → e ↦ e' → e' ↦* e'' → e ↦* e''
  
Env : ℕ → Set
Env m = Subs m × ExpM 0 m

data _⇝M_ {m : ℕ} : Env m → Env m → Set where
  var : {σ : Subs m}{x : Fin m}{s s' : Sub} → let s = lookup x σ in 
             {p : SubVar} → 
             s [ p ]:= s' → 
             (σ , mvar x p) ⇝M (σ , conv x p s')
--  varS : {σ : Subs m}{x : Fin m}{s : Sub} → let s = lookup x σ in 
--             {p : SubVar} → 
--             s [ p ]:= just (S unit) → 
--             (σ , mvar x p) ⇝M (σ , S (mvar x (there p)))
  bind0 : {σ : Subs m}{x : Fin m} → let s = lookup x σ in 
           {p : SubVar} → s [ p ]:= hole → 
          (σ , mvar x p) ⇝M (update x (updateS Z p) σ , Z) 
  bindS : {σ : Subs m}{x : Fin m} → let s = lookup x σ in 
    {p : SubVar} → s [ p ]:= hole → 
    (σ , mvar x p) ⇝M (update x (updateS (S hole) p) σ , S (mvar x (there p)))
    

data _⇝R_ {m : ℕ} : Env m → Env m → Set where
  lift : {σ : Subs m}{e e' : ExpM 0 m} → e ↦R e' → (σ , e) ⇝R (σ , e')
  meta : {σ σ' : Subs m}{e e' e'' e₀ : ExpM 0 m}{eₛ : ExpM 1 m} → (σ , e) ⇝M (σ' , e') → 
               case e' alt₀ e₀ altₛ eₛ ↦R e'' → 
               (σ , case e alt₀ e₀ altₛ eₛ) ⇝R (σ' , e'')
               


----embVar : ∀{V M}{σ σ' : Subs m}
----                                        
--
⇝M-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} →   (σ , e) ⇝M (σ' , e') → σ ≤s σ'
⇝M-mono (var x₁) = ≤s-refl
⇝M-mono (bind0 {x = x} i) = upd-point x (upd-mono i)
⇝M-mono (bindS {x = x} i) = upd-point x (upd-mono i)

⇝R-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝R (σ' , e') → σ ≤s σ'
⇝R-mono (lift x) = ≤s-refl
⇝R-mono (meta r x) = ⇝M-mono r

⇝M-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝M (σ' , e') → e ∈E σ → e' ∈E σ'
⇝M-in (var i) (mvar x₁) = {!!}
⇝M-in (bind0 x₁) x₂ = Z
⇝M-in {σ = σ} (bindS x₁) (mvar {x = x} {p} x₂) = {!!}
-- S (mvar (subst (_∈ₛ_ (there p)) (upd-look x (updateS (S here) p) σ) (updS-var x₁ x₂)))

--⇝R-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝R (σ' , e') → e ∈E σ → e' ∈E σ'
--⇝R-in (lift x) i = ↦R-in x i
--⇝R-in (meta x x₁) (case i alt₀ i₁ altₛ i₂) =  ↦R-in x₁ (case ⇝M-in x i alt₀ emb-exp (⇝M-mono x) i₁ altₛ emb-exp (⇝M-mono x) i₂)
--
--_⟪_⟫ : ∀{V M} → (e : ExpM V M) → (τ : Subs M) → ExpM V M
--Z ⟪ ns ⟫ = Z
--S e ⟪ ns ⟫ = S (e ⟪ ns ⟫)
--var x ⟪ ns ⟫ = var x
--mvar x p ⟪ ns ⟫ = natToExp x p (lookup x ns) 
--(case e alt₀ e₁ altₛ e₂) ⟪ ns ⟫ =
--      case e ⟪ ns ⟫ alt₀ e₁ ⟪ ns ⟫ altₛ e₂ ⟪ ns ⟫
--      
--sub-eq : ∀{m v}{e : ExpM v m}{σ : Subs m} → {i i' : e ∈E σ} →  e ⟪ σ ⟫ ≡ e ⟪ σ ⟫
--sub-eq {i = i} {i'} with ∈E-uniq i i'
--sub-eq | refl = refl
--
--suc-natToExp :  ∀{V V' M} {x : Fin M} {p : SubVar}(s : Sub)(p' : SubVar) → sucExp {V' = V'} V (natToExp' x p s p') ≡ natToExp' x p s p'
--suc-natToExp hole  here = refl
--suc-natToExp hole  (there p') = refl 
--suc-natToExp Z     a = refl 
--suc-natToExp (S s) here = cong S (suc-natToExp s here) 
--suc-natToExp (S s) (there p') = suc-natToExp s p'
--
--sub-natToExp : ∀{V V' M}{e : ExpM V' M}{x : Fin M}{p : SubVar}(s : Sub)(p' : SubVar) → sub V (natToExp' x p s p') e ≡ natToExp' x p s p'
--sub-natToExp hole here = refl
--sub-natToExp hole (there p₁) = refl
--sub-natToExp Z a = refl
--sub-natToExp (S s) here = cong S (sub-natToExp s here) 
--sub-natToExp (S s) (there p₁) = sub-natToExp s p₁
--
--sucExp-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : ExpM (V + V') M) → sucExp V (e ⟪ σ ⟫) ≡ sucExp V e ⟪ σ ⟫  
--sucExp-subs V Z = refl
--sucExp-subs V (S i) = cong S (sucExp-subs V i)
--sucExp-subs V (var v) = refl
--sucExp-subs V {σ = σ} (mvar x p) = suc-natToExp (lookup x σ) p
--sucExp-subs V (case i alt₀ i₁ altₛ i₂) = cong₃ case_alt₀_altₛ_ (sucExp-subs V i) (sucExp-subs V i₁) (sucExp-subs (suc V) i₂)
--      
--sub-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : ExpM (V + suc V') M) → (e' : ExpM V' M) → sub V (e ⟪ σ ⟫) (e' ⟪ σ ⟫) ≡ sub V e e' ⟪ σ ⟫  
--sub-subs V Z i' = refl
--sub-subs V (S i) i' = cong S (sub-subs V i i')
--sub-subs zero (var zero) i' = refl
--sub-subs zero (var (suc v)) i' = refl
--sub-subs (suc V) (var (zero)) i' = refl
--sub-subs (suc V) (var (suc v)) i' with sub-subs V (var v) i' 
--... | p = trans (cong (sucExp 0) p) (sucExp-subs zero (sub V (var v) i')) -- cong (sucExp 0) p
--sub-subs V {σ = σ} (mvar x p) i' = sub-natToExp (lookup x σ) p
--sub-subs V (case i alt₀ i₁ altₛ i₂) i' = cong₃ case_alt₀_altₛ_ (sub-subs V i i') (sub-subs V i₁ i') (sub-subs (suc V) i₂ i')
--     
--↦R-subs : ∀{m}{e e' : ExpM 0 m} → (r : e ↦R e') → (σ : Subs m) →  e ⟪ σ ⟫ ↦R e' ⟪ σ ⟫
--↦R-subs (caseZ e e') σ = caseZ (e ⟪ σ ⟫) (e' ⟪ σ ⟫)
--↦R-subs (caseS {ef = ef} e e'') σ  = 
--        subst (λ e' → (case S (ef ⟪ σ ⟫) alt₀ e ⟪ σ ⟫ altₛ (e'' ⟪ σ ⟫)) ↦R e' ) (sub-subs 0 e'' ef) (caseS (e ⟪ σ ⟫) (e'' ⟪ σ ⟫)) -- caseS ? {!caseS!}
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
--      
--⇝R-sound :  ∀{M}{τ : Subs M}{e e' : ExpM 0 M} → (σ : Subs M)
--                    (i : e ∈E σ) → (r : (σ , e) ⇝R (τ , e')) →  
--            (e ⟪ τ ⟫ ) ↦R (e' ⟪ τ ⟫ )
--⇝R-sound {e = e}{e'} σ i (lift x) = ↦R-subs x σ
--⇝R-sound σ (case i alt₀ i₁ altₛ i₂) (meta (varZ x₁) (caseZ e' e'')) = 
--         subst (λ x → case x alt₀ e' ⟪ σ ⟫ altₛ e'' ⟪ σ ⟫ ↦R (e' ⟪ σ ⟫)) (lookupZ x₁) 
--           (caseZ (e' ⟪ σ ⟫) (e'' ⟪ σ ⟫))
--⇝R-sound σ (case i alt₀ i₁ altₛ i₂) (meta (varS {x = x}{p = p} x₁) (caseS e' e'')) = {!!}
--⇝R-sound σ (case i alt₀ i₁ altₛ i₂) (meta (bind0 x₁) (caseZ e' e'')) = {!!}
--⇝R-sound σ (case i alt₀ i₁ altₛ i₂) (meta (bindS x₁) (caseS e' e'')) = {!!}



--getOrd : ∀{m}{σ σ' : Subs m} → σ ≤s σ' → (x : Fin m) → lookup x σ ≤N lookup x σ'
--getOrd (x ∷ o) zero = x
--getOrd (_ ∷ o) (suc x) = getOrd o x
--
--
----embCxt : ∀{m V}{M N : Subs m} → Cxt V M → M ≤s N → ExpM V N → ExpM V N
----embCxt hole o e = e
----embCxt (case H alt₀ e' altₛ e'') o e = case (embCxt H o e) alt₀ (embExp o e') altₛ embExp o e''
----
----repl : ∀{V m}(τ : Subs m) → (VecI Nohole τ) → ExpM V τ →  Exp V
----repl τ is (nat Z) = nat Z
----repl τ is (nat (S e)) = nat (S (repl τ is e))
----repl τ is (var x) = var x
----repl (a ∷ τ) (x ∷ is) (mvar zero p) = natToExp (a , x) p
----repl (a ∷ τ) (x ∷ is) (mvar (suc x₁) p) = repl τ is (mvar x₁ p)
----repl τ is (case e alt₀ e₁ altₛ e₂) = case repl τ is e alt₀ repl τ is e₁ altₛ repl τ is e₂
--
--
--data _⇝_ {m : ℕ} : Env m → Env m → Set where
--  prom : {σ σ' : Subs m}{e e' : ExpM 0 m} → 
--         (r : (σ , e) ⇝R (σ' , e')) → (H : Cxt 0 m)  → 
--           (σ , H [/ e ]) ⇝ (σ' , H [/ e' ])
--           
--⇝-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝ (σ' , e') → σ ≤s σ'
--⇝-mono (prom r H) = ⇝R-mono r
--
--⇝-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝ (σ' , e') → e ∈E σ → e' ∈E σ'
--⇝-in (prom r hole) o = ⇝R-in r o
--⇝-in (prom r (case H alt₀ e'' altₛ e''')) (case o alt₀ o₁ altₛ o₂) = 
--           case ⇝-in (prom r H) o alt₀ emb-exp (⇝R-mono r) o₁ altₛ emb-exp (⇝R-mono r) o₂
--
--data _⇝*_ {m : ℕ} : Env m → Env m → Set where
--  [] : {s : Env m} → s ⇝* s
--  _∷_ : {s s' s'' : Env m} → (r : s ⇝ s') → (rs : s' ⇝* s'') → s ⇝* s''
--  
--⇝*-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝* (σ' , e') → σ ≤s σ'
--⇝*-mono [] = ≤s-refl
--⇝*-mono (r ∷ rs) = ≤s-trans (⇝-mono r) (⇝*-mono rs)
--  
--⇝*-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝* (σ' , e') → e ∈E σ → e' ∈E σ'
--⇝*-in [] o = o
--⇝*-in (r ∷ r₁) o = ⇝*-in r₁ (⇝-in r o)
--
--data _⇝!_ {m : ℕ} : Env m → Env m → Set where
--  fill : {σ τ : Subs m}{e : ExpM 0 m}{s : Env m} → VecI Nohole τ → (o : σ ≤s τ) →
--       (r : s ⇝* (σ , e)) →  s ⇝! (τ ,  e)
--       
--inp! : ∀{m}{τ : Subs m} {e : ExpM 0 m}{s : Env m} → s ⇝! (τ , e) → VecI Nohole τ
--inp! {s = proj₁ , proj₂} (fill x o x₁) = x
--






--⇝!-mono : ∀{m}{σ τ : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝! (τ , e') → σ ≤s τ
--⇝!-mono (fill x o r) = ≤s-trans (⇝*-mono r) o 
--
--⇝!-in : ∀{m}{σ τ : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝! (τ , e') → e ∈E σ → e' ∈E τ
--⇝!-in (fill x o r) i = emb-exp o (⇝*-in r i)
--
--⇝*-sound :  ∀{M}{σ τ : Subs M}{e e' : ExpM 0 M} → 
--                    (i : e ∈E σ) → (r : (σ , e) ⇝* (τ , e')) →  
--            (e ⟪ τ , emb-exp (⇝*-mono r) i ⟫ ) ↦* (e' ⟪ τ , ⇝*-in r i ⟫ )
--⇝*-sound i [] = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (lift x) H) r₁) = {!i!} -- {!!} ∷ {!⇝*-sound i r₁!}
--⇝*-sound i (_∷_ {s' = ._ , .(H [/ Z ])} (prom (varZ x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (varS x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , .(H [/ Z ])} (prom (bind0 x₁) H) r₁) = {!!}
--⇝*-sound i (_∷_ {s' = ._ , ._} (prom (bindS x₁) H) r₁) = {!!}


--⇝!-sound : ∀{M}{σ τ : Subs M}{e e' : ExpM 0 M} → 
--                    (i : e ∈E σ) → (r : (σ , e) ⇝! (τ , e')) →  
--            (e ⟪ τ , inp! r , emb-exp (⇝!-mono r) i ⟫) ↦* (e' ⟪ τ , inp! r , ⇝!-in r i ⟫)
--⇝!-sound {τ = τ} {e} i (fill x o []) = subst (λ o' → e ⟪ τ , x , emb-exp o' i ⟫ ↦* e ⟪ τ , x , emb-exp o i ⟫) ≤s-trans-refl []
--⇝!-sound i (fill x o (_∷_ {s' = σ' , ._} (prom r H) r₁)) = {!r!} 
