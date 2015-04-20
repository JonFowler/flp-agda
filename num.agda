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


conv : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → ExpM V M
conv x p hole = mvar x p
conv x p Z = Z
conv x p (S s) = S (conv x (there p) s)

conv-in : ∀{M V}{σ : Subs M}{x : Fin M}{s' : Sub}{p : SubVar}  →
        (lookup x σ [ p ]:= s' ) → conv {V = V} x p s' ∈E σ
conv-in {s' = hole} i = mvar (look-in i)
conv-in {s' = Z} i = Z
conv-in {s' = S s'} i = S (conv-in (look-S i))

  
--subToExp : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → 
--            (p' : SubVar) →  ExpM V M
--subToExp x p hole here = mvar x p
--subToExp x p hole (there w) = Z
--subToExp x p Z _ = Z
--subToExp x p (S s) here = S (subToExp x (there p) s here)
--subToExp x p (S s) (there p₁) = subToExp x p s p₁  
--
--
--
--subToExp-in : ∀{M V}{σ : Subs M}{x : Fin M}{p : SubVar} → (p ∈ₛ lookup x σ) → (s : Sub) → 
--            (p' : SubVar) → subToExp {V = V} x p s p' ∈E σ
--subToExp-in i hole here = mvar i
--subToExp-in i hole (there p') = Z
--subToExp-in i Z p' = Z
--subToExp-in i (S s) here = S (subToExp-in {!!} s here)
--subToExp-in i (S s) (there p') = subToExp-in i s p'

toExp : ∀{M V} (x : Fin M) → (p : SubVar) → (s : Sub) → ExpM V M
toExp x p s = conv x p (getSub p s) 

toExp-in : ∀{M V}{σ : Subs M}{x : Fin M}{p : SubVar} → (p ∈ₛ lookup x σ) → 
         toExp {V = V} x p (lookup x σ) ∈E σ 
toExp-in i = conv-in (getSub-in i) 

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
  
data _↦R_ {V M : ℕ} : ExpM V M → ExpM V M → Set where
  caseZ :  (e : ExpM V M) → (e' : ExpM (suc V) M) → case Z alt₀ e altₛ e' ↦R e
  caseS : {ef : ExpM V M} → (e : ExpM V M) → (e' : ExpM (suc V) M)   
                → case (S ef) alt₀ e altₛ e' ↦R e' [- ef -]
                
↦R-in : ∀{M}{σ : Subs M}{e e' : ExpM 0 M} → e ↦R  e' → e ∈E σ → e' ∈E σ
↦R-in (caseZ e' e'') (case e₁ alt₀ e₂ altₛ e₃) = e₂
↦R-in (caseS e' e'') (case S e₁ alt₀ e₂ altₛ e₃) = sub-in 0 e₃ e₁

--data Cxt (V : ℕ) (M : ℕ)  : Set where
--  hole : Cxt V M
--  case_alt₀_altₛ_ : Cxt V M → ExpM V M → ExpM (suc V) M → Cxt V M
  
--_[/_] : ∀{M V} → Cxt V M → ExpM V M → ExpM V M
--hole [/ e ] = e
--(case H alt₀ x altₛ x₁) [/ e ] = case H [/ e ] alt₀ x altₛ x₁
  
data _↦_ {V M : ℕ} : ExpM V M → ExpM V M → Set where
  pure : {e e' : ExpM V M} → e ↦R e' → e ↦ e' 
  subj : {e e' e₀ : ExpM V M}{eₛ : ExpM (suc V) M} → e ↦ e' → 
               case e alt₀ e₀ altₛ eₛ ↦ case e' alt₀ e₀ altₛ eₛ

data _↦*_ {V M : ℕ} : ExpM V M → ExpM V M → Set where
  [] : {e : ExpM V M} → e ↦* e
  _∷_ : {e e' e'' : ExpM V M} → e ↦ e' → e' ↦* e'' → e ↦* e''
  
Env : ℕ → ℕ → Set
Env V M = Subs M × ExpM V M

data _⇝M_ {V M : ℕ} : Env V M → Env V M → Set where
  mvar : {σ : Subs M}{x : Fin M}{p : SubVar}{s : Sub} → let s = lookup x σ in  
          --   s [ p ]:= s' → 
             (σ , mvar x p) ⇝M (σ , toExp x p s)   --conv x p s')
--  varS : {σ : Subs m}{x : Fin m}{s : Sub} → let s = lookup x σ in 
--             {p : SubVar} → 
--             s [ p ]:= just (S unit) → 
--             (σ , mvar x p) ⇝M (σ , S (mvar x (there p)))
  bind0 : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
           {p : SubVar} → s [ p ]:= hole → 
          (σ , mvar x p) ⇝M (update x (updateS Z p) σ , Z) 
  bindS : {σ : Subs M}{x : Fin M} → let s = lookup x σ in 
    {p : SubVar} → s [ p ]:= hole → 
    (σ , mvar x p) ⇝M (update x (updateS (S hole) p) σ , S (mvar x (there p)))
    

data _⇝R_ {V M : ℕ} : Env V M → Env V M → Set where
  lift : {σ : Subs M}{e e' : ExpM V M} → e ↦R e' → (σ , e) ⇝R (σ , e')
  meta : {σ σ' : Subs M}{e e' e'' e₀ : ExpM V M}{eₛ : ExpM (suc V) M} → (σ , e) ⇝M (σ' , e') → 
               case e' alt₀ e₀ altₛ eₛ ↦R e'' → 
               (σ , case e alt₀ e₀ altₛ eₛ) ⇝R (σ' , e'')
               


----embVar : ∀{V M}{σ σ' : Subs m}
----                                        
--
⇝M-mono : ∀{M V}{σ σ' : Subs M}{e e' : ExpM V M} →   (σ , e) ⇝M (σ' , e') → σ ≤s σ'
⇝M-mono mvar = ≤s-refl
⇝M-mono (bind0 {x = x} i) = upd-point x (upd-mono i)
⇝M-mono (bindS {x = x} i) = upd-point x (upd-mono i)

⇝R-mono : ∀{V M}{σ σ' : Subs M}{e e' : ExpM V M} → (σ , e) ⇝R (σ' , e') → σ ≤s σ'
⇝R-mono (lift x) = ≤s-refl
⇝R-mono (meta r x) = ⇝M-mono r

⇝M-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝M (σ' , e') → e ∈E σ → e' ∈E σ'
⇝M-in mvar (mvar x₁) = toExp-in x₁ 
⇝M-in (bind0 x₁) x₂ = Z
⇝M-in {σ = σ} (bindS x₁) (mvar {x = x} {p} x₂) =  
  S (mvar (subst (_∈ₛ_ (there p)) (upd-look x (updateS (S hole) p) σ) (look-in (look-S (updS-var x₂))) )) -- (updS-var x₁ x₂)))

⇝R-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝R (σ' , e') → e ∈E σ → e' ∈E σ'
⇝R-in (lift x) i = ↦R-in x i
⇝R-in (meta x x₁) (case i alt₀ i₁ altₛ i₂) =  ↦R-in x₁ (case ⇝M-in x i alt₀ emb-exp (⇝M-mono x) i₁ altₛ emb-exp (⇝M-mono x) i₂)

_⟪_⟫ : ∀{V M} → (e : ExpM V M) → (τ : Subs M) → ExpM V M
Z ⟪ ns ⟫ = Z
S e ⟪ ns ⟫ = S (e ⟪ ns ⟫)
var x ⟪ ns ⟫ = var x
mvar x p ⟪ ns ⟫ = toExp x p (lookup x ns) 
(case e alt₀ e₁ altₛ e₂) ⟪ ns ⟫ =
      case e ⟪ ns ⟫ alt₀ e₁ ⟪ ns ⟫ altₛ e₂ ⟪ ns ⟫
     
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

subs-idem : ∀{V M} {τ : Subs M} → (e : ExpM V M) → e ⟪ τ ⟫ ≡ (e ⟪ τ ⟫) ⟪ τ ⟫
subs-idem Z = refl
subs-idem (S e) = cong S (subs-idem e)
subs-idem (var x) = refl
subs-idem {τ = τ} (mvar x p) = conv-subs p (getSub p (lookup x τ)) refl
subs-idem (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-idem e) (subs-idem e₁) (subs-idem e₂)

conv-over : ∀{V M} {τ : Subs M}{x : Fin M}(p : SubVar) → (s s' : Sub) → (s ≤ₛ s') → s' ≡ getSub p (lookup x τ) → conv {V = V} x p s' ≡ conv {V = V} x p s ⟪ τ ⟫
conv-over {x = x} p hole s' o eq = cong (conv x p) eq
conv-over p Z Z ≤Z eq = refl
conv-over p (S s) (S s') (≤S o) eq = cong S (conv-over (there p) s s' o (getSub-up {p} eq))

subs-over : ∀{V M} {σ τ : Subs M} → σ ≤s τ → (e : ExpM V M) → e ⟪ τ ⟫ ≡ (e ⟪ σ ⟫) ⟪ τ ⟫
subs-over o Z = refl
subs-over o (S e) = cong S (subs-over o e)
subs-over o (var x) = refl
subs-over {σ = σ}{τ}  o (mvar x p) = conv-over p (getSub p (lookup x σ)) (getSub p (lookup x τ)) (getSub-mono p (lookupI₂ x o)) refl -- conv-subs p (getSub p (lookup x σ)) ?
subs-over o (case e alt₀ e₁ altₛ e₂) = cong₃ case_alt₀_altₛ_ (subs-over o e) (subs-over o e₁) (subs-over o e₂)
      
--sub-eq : ∀{m v}{e : ExpM v m}{σ : Subs m} → {i i' : e ∈E σ} →  e ⟪ σ ⟫ ≡ e ⟪ σ ⟫
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

sub-conv : ∀{V V' M}{e : ExpM V' M}{x : Fin M}{p : SubVar}(s : Sub) → 
         sub V (conv x p s) e ≡ conv x p s
sub-conv hole = refl
sub-conv Z = refl
sub-conv {V} (S s) = cong S (sub-conv {V} s)

sub-toExp : ∀{V V' M}{e : ExpM V' M}{x : Fin M}(p : SubVar)(s : Sub) → 
         sub V (toExp x p s) e ≡ toExp x p s
sub-toExp p s = sub-conv (getSub p s)

--sub-natToExp : ∀{V V' M}{e : ExpM V' M}{x : Fin M}{p : SubVar}(s : Sub)(p' : SubVar) → sub V (natToExp' x p s p') e ≡ natToExp' x p s p'
--sub-natToExp hole here = refl
--sub-natToExp hole (there p₁) = refl
--sub-natToExp Z a = refl
--sub-natToExp (S s) here = cong S (sub-natToExp s here) 
--sub-natToExp (S s) (there p₁) = sub-natToExp s p₁
--
sucExp-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : ExpM (V + V') M) → sucExp V (e ⟪ σ ⟫) ≡ sucExp V e ⟪ σ ⟫  
sucExp-subs V Z = refl
sucExp-subs V (S i) = cong S (sucExp-subs V i)
sucExp-subs V (var v) = refl
sucExp-subs V {σ = σ} (mvar x p) = suc-toExp p (lookup x σ)
sucExp-subs V (case i alt₀ i₁ altₛ i₂) = cong₃ case_alt₀_altₛ_ (sucExp-subs V i) (sucExp-subs V i₁) (sucExp-subs (suc V) i₂)
      
sub-subs : {V' M : ℕ}(V : ℕ){σ : Subs M} → (e : ExpM (V + suc V') M) → (e' : ExpM V' M) → sub V (e ⟪ σ ⟫) (e' ⟪ σ ⟫) ≡ sub V e e' ⟪ σ ⟫  
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
↦R-subs : ∀{M V}{e e' : ExpM V M} → (r : e ↦R e') → (σ : Subs M) →  e ⟪ σ ⟫ ↦R e' ⟪ σ ⟫
↦R-subs (caseZ e e') σ = caseZ (e ⟪ σ ⟫) (e' ⟪ σ ⟫)
↦R-subs (caseS {ef = ef} e e'') σ  = subst (λ e' → (case S (ef ⟪ σ ⟫) alt₀ e ⟪ σ ⟫ altₛ (e'' ⟪ σ ⟫)) ↦R e' ) (sub-subs 0 e'' ef) (caseS (e ⟪ σ ⟫) (e'' ⟪ σ ⟫)) -- caseS ? {!caseS!}


↦R-over : ∀{M}{e e' : ExpM 0 M}{σ σ' : Subs M} → 
        (σ ≤s σ') → (e ⟪ σ ⟫ ↦R e' ⟪ σ ⟫ )  →  e ⟪ σ' ⟫ ↦R e' ⟪ σ' ⟫
↦R-over {e = e}{e'}{σ}{σ'} o r = subst₂ (λ x x₁ → x ↦R x₁) 
        (sym (subs-over o e)) (sym (subs-over o e')) (↦R-subs r σ')
        
        
↦-subs : ∀{m}{e e' : ExpM 0 m} → (r : e ↦ e') → (σ : Subs m) →  e ⟪ σ ⟫ ↦ e' ⟪ σ ⟫
↦-subs (pure x) σ = pure (↦R-subs x σ)
↦-subs (subj r) σ = subj (↦-subs r σ)

↦-over : ∀{M}{e e' : ExpM 0 M}{σ σ' : Subs M} → 
        (σ ≤s σ') → (e ⟪ σ ⟫ ↦ e' ⟪ σ ⟫ )  →  e ⟪ σ' ⟫ ↦ e' ⟪ σ' ⟫
↦-over {e = e}{e'}{σ}{σ'} o r = subst₂ (λ x x₁ → x ↦ x₁) 
        (sym (subs-over o e)) (sym (subs-over o e')) (↦-subs r σ')

↦*-subs : ∀{m}{e e' : ExpM 0 m} → (r : e ↦* e') → (σ : Subs m) →  e ⟪ σ ⟫ ↦* e' ⟪ σ ⟫
↦*-subs [] σ = []
↦*-subs (x ∷ r) σ = (↦-subs x σ) ∷ ↦*-subs r σ

↦*-over : ∀{M}{e e' : ExpM 0 M}{σ σ' : Subs M} → 
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

toExp-upd : ∀{p s s' M V}{x : Fin M} → (p ∈ₛ s') →  conv {V = V} x p s ≡ toExp x p (updateS s p s')
toExp-upd {p}{x = x} i = cong (conv x p) (getSub-upd i)

⇝R-sound :  ∀{M V}{τ : Subs M}{e e' : ExpM V M} → (σ : Subs M)
                    (i : e ∈E σ) → (r : (σ , e) ⇝R (τ , e')) →  
            (e ⟪ τ ⟫ ) ↦R (e' ⟪ τ ⟫ )
⇝R-sound σ i (lift x) = ↦R-subs x σ
⇝R-sound σ (case (mvar{x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta mvar x') 
     with getSub p (lookup x σ) | inspect (getSub p) (lookup x σ)
⇝R-sound σ (case mvar x₁ alt₀ i₁ altₛ i₂) (meta mvar ()) | hole | eq 
⇝R-sound σ (case mvar x₁ alt₀ i₁ altₛ i₂) (meta mvar (caseZ e e')) | Z | eq = caseZ (e ⟪ σ ⟫) (e' ⟪ σ ⟫)
⇝R-sound σ (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta mvar (caseS e e'')) | S s | [ eq ]
   = let ef = conv x (there p) s
         r = caseS {ef = ef} (e ⟪ σ ⟫) (e'' ⟪ σ ⟫) 
         eq1 = cong (sub 0 (e'' ⟪ σ ⟫)) (conv-subs (there p) s (getSub-up {p}{lookup x σ} (sym eq))) 
         eq2 = sub-subs 0 {σ = σ} e'' ef in 
       subst (λ x₂ → case (S ef) alt₀ e ⟪ σ ⟫ altₛ e'' ⟪ σ ⟫ ↦R x₂) 
           (trans eq1 eq2 ) r
⇝R-sound σ (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta (bind0 x₂) (caseZ e' e'')) = 
   let τ = update x (updateS Z p) σ 
       r = caseZ (e' ⟪ τ ⟫) (e'' ⟪ τ ⟫)
   in subst (λ x₂ → case x₂ alt₀ e' ⟪ τ ⟫ altₛ e'' ⟪ τ ⟫ ↦R e' ⟪ τ ⟫) 
               (trans (toExp-upd x₁) (cong (toExp x p) (upd-look x (updateS Z p) σ))) r
⇝R-sound σ (case (mvar {x = x}{p} x₁) alt₀ i₁ altₛ i₂) (meta (bindS x₂) (caseS e e'')) = 
   let τ = update x (updateS (S hole) p) σ 
       r = caseS {ef = mvar x (there p)} (e ⟪ τ ⟫) (e'' ⟪ τ ⟫)
       eq1 = toExp-upd x₁
       eq2 = cong (toExp x p) (upd-look x (updateS (S hole) p) σ)
       eq1'' = cong (toExp x (there p)) (upd-look x (updateS (S hole) p) σ)
       eq1' = cong (sub zero (e'' ⟪ τ ⟫)) 
              (trans (cong (conv x (there p)) (getSub-there {p} (getSub-upd x₁))) eq1'') 
       eq2' = sub-subs zero e'' (mvar x (there p))
   in subst₂ (λ es er → case es alt₀ e ⟪ τ ⟫ altₛ e'' ⟪ τ ⟫ ↦R er) 
                (trans eq1 eq2) (trans eq1' eq2') r 
                

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
data _⇝_ {V M : ℕ} : Env V M → Env V M → Set where
  pure : {σ σ' : Subs M}{e e' : ExpM V M} → (r : (σ , e) ⇝R (σ' , e')) →
             (σ , e) ⇝ (σ' , e')
  subj : {σ σ' : Subs M}{e e' e₀ : ExpM V M}{eₛ : ExpM (suc V) M} → 
         (r : (σ , e) ⇝ (σ' , e')) → 
           (σ , case e alt₀ e₀ altₛ eₛ) ⇝ (σ' , case e' alt₀ e₀ altₛ eₛ)
           
∈E-subj : ∀{V M}{e e' : ExpM V M}{e'' : ExpM (suc V) M}{σ : Subs M} → case e alt₀ e' altₛ e'' ∈E σ → e ∈E σ
∈E-subj (case i alt₀ i₁ altₛ i₂) = i

--_⟪cxt|_⟫ : ∀{V M} → Cxt V M → Subs M → Cxt V M
--hole ⟪cxt| σ ⟫ = hole
--(case H alt₀ x altₛ x₁) ⟪cxt| σ ⟫ = case H ⟪cxt| σ ⟫ alt₀ x ⟪ σ ⟫ altₛ x₁ ⟪ σ ⟫
--
--cxt-sub :  ∀{V M}{e : ExpM V M}{σ : Subs M} → (H : Cxt V M) →  
--        H [/ e ] ⟪ σ ⟫ ≡ H ⟪cxt| σ ⟫ [/ e ⟪ σ ⟫ ]
--cxt-sub hole = refl
--cxt-sub {σ = σ} (case H alt₀ x altₛ x₁) = cong (λ h → case h alt₀ x ⟪ σ ⟫ altₛ x₁ ⟪ σ ⟫) (cxt-sub H)
           

--⇝-red :  ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → 
--         (σ , H [/ e ]) ⇝ (σ' , H [/ e' ]) → (σ , e) ⇝R (σ' , e')
--⇝-red {e = e}{H = hole} r = {!e!}
--⇝-red {H = case H alt₀ x altₛ x₁} r = {!!}
           
⇝-sound :  ∀{M V}{τ : Subs M}{e e' : ExpM V M} → (σ : Subs M)
                    (i : e ∈E σ) → (r : (σ , e) ⇝ (τ , e')) →  
            (e ⟪ τ ⟫ ) ↦ (e' ⟪ τ ⟫ )
⇝-sound σ i (pure r) = pure (⇝R-sound σ i r)
⇝-sound σ (case i alt₀ i₁ altₛ i₂) (subj r) = subj (⇝-sound σ i r)

           
⇝-mono : ∀{M V}{σ σ' : Subs M}{e e' : ExpM V M} → (σ , e) ⇝ (σ' , e') → σ ≤s σ'
⇝-mono (pure r) = ⇝R-mono r
⇝-mono (subj r) = ⇝-mono r

⇝-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝ (σ' , e') → e ∈E σ → e' ∈E σ'
⇝-in (pure r) x = ⇝R-in r x
⇝-in (subj r) (case x alt₀ x₁ altₛ x₂) = 
     case ⇝-in r x alt₀ emb-exp (⇝-mono r) x₁ altₛ emb-exp (⇝-mono r) x₂
--
data _⇝*_ {V M : ℕ} : Env V M → Env V M → Set where
  [] : {s : Env V M} → s ⇝* s
  _∷_ : {σ σ' σ'' : Subs M}{e e' e'' : ExpM V M} → (r : (σ , e) ⇝ (σ' , e')) → (rs : (σ' , e') ⇝* (σ'' , e'')) → (σ , e) ⇝* (σ'' , e'')
  
⇝*-mono : ∀{M V}{σ σ' : Subs M}{e e' : ExpM V M} → (σ , e) ⇝* (σ' , e') → σ ≤s σ'
⇝*-mono [] = ≤s-refl
⇝*-mono (r ∷ rs) = ≤s-trans (⇝-mono r) (⇝*-mono rs)
  
⇝*-sound :  ∀{M}{τ : Subs M}{e e' : ExpM 0 M} → (σ : Subs M)
                    (i : e ∈E σ) → (σ , e) ⇝* (τ , e') → (e ⟪ τ ⟫ ) ↦* (e' ⟪ τ ⟫ )
⇝*-sound τ i [] = []
⇝*-sound {τ = τ} σ i (_∷_ {σ = .σ}{σ'}{.τ}{e}{e'}{e''} r r₁) =  
  ↦-over {e = e}{e' = e'} (⇝*-mono r₁) (⇝-sound σ i r) ∷ ⇝*-sound σ' (⇝-in r i) r₁
  

  
 
--⇝*-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝* (σ' , e') → e ∈E σ → e' ∈E σ'
--⇝*-in [] o = o
--⇝*-in (r ∷ r₁) o = ⇝*-in r₁ (⇝-in r o)

--
data _⇝!_ {V M : ℕ} : Env V M → Env V M → Set where
  fill : {σ σ' τ : Subs M}{e e' : ExpM V M} → Inps τ → (o : σ' ≤s τ) →
       (r : (σ , e) ⇝* (σ' , e')) →  (σ , e) ⇝! (τ ,  e')
       
⇝!-sound :  ∀{M}{τ : Subs M}{e e' : ExpM 0 M} → (σ : Subs M)
                    (i : e ∈E σ) → (σ , e) ⇝! (τ , e') → (e ⟪ τ ⟫ ) ↦* (e' ⟪ τ ⟫ )
⇝!-sound σ i (fill {e = e}{e'} x o r) =  ↦*-over {e = e}{e' = e'} o (⇝*-sound σ i r)

       
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
