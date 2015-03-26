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


data Nat (A : Set) : Set where
  Z : Nat A
  S : A → Nat A
  
 
mapNat : {A B : Set} → (A → B) → Nat A → Nat B
mapNat f Z = Z
mapNat f (S x) =  S (f x) 
  
data NatSub : Set where
  hole : NatSub
  Z : NatSub
  S : NatSub → NatSub
  
Subs : ℕ → Set
Subs = Vec NatSub 
  
data Nohole : NatSub → Set where
  Z : Nohole Z
  S : {n : NatSub} → Nohole n → Nohole (S n)
  
Noholes : ∀{M} → Subs M → Set
Noholes σ = VecI Nohole σ
  
Input : Set
Input = Σ NatSub Nohole
  
Inputs : ℕ → Set
Inputs m = Vec Input m
  
data NatVar : Set where
  here : NatVar 
  there : (p : NatVar) → NatVar 
  
data _∈ₛ_ : NatVar → NatSub → Set where
  here : ∀{s} → here ∈ₛ s
  there : ∀{p s} → p ∈ₛ s → there p ∈ₛ S s
  
updZ : NatVar → NatSub → NatSub
updZ here s = Z 
updZ (there p) (S n) = S (updZ p n)
updZ  _ _ = Z

updS :  NatVar → NatSub → NatSub 
updS here s = S hole 
updS (there p) (S n) = S (updS p n)
updS _  _ = Z 

data _[_]:=_ : (s : NatSub) → NatVar → Maybe (Nat Unit) → Set where 
  hereZ : Z [ here ]:= just Z 
  hereS : {a : NatSub} → S a [ here ]:= just (S unit) 
  hereH : hole [ here ]:= nothing
  thereZ : {s : NatSub}{p : NatVar} → s [ p ]:=  just Z → S s [ there p ]:= just Z 
  thereS : {s : NatSub}{p  : NatVar} → s [ p ]:=  just (S unit) → 
                S s [ there p ]:= just (S unit) 
  thereH : {s : NatSub}{p : NatVar} → s [ p ]:= nothing → S s [ there p ]:= nothing

 
data ExpM (V : ℕ) (M : ℕ) : Set where
  Z : ExpM V M
  S :  ExpM V M → ExpM V M
  var : Fin V → ExpM V M
  mvar : (x : Fin M) → (p : NatVar )  → ExpM V M 
  case_alt₀_altₛ_ : ExpM V M → ExpM V M → ExpM (suc V) M → ExpM V M
  
data _∈E_ {V M : ℕ} : ExpM V M → Subs M → Set where
  Z : ∀{σ} → Z ∈E σ
  S : ∀{e σ} → e ∈E σ → S e ∈E σ
  var : ∀{v σ} → var v ∈E σ
  mvar : ∀{σ}{x : Fin M}{p : NatVar} → p ∈ₛ lookup x σ  → mvar x p ∈E σ
  case_alt₀_altₛ_ : ∀{e e' e'' σ} → e ∈E σ → e' ∈E σ → e'' ∈E σ → case e alt₀ e' altₛ e'' ∈E σ 
  
Exp : (V : ℕ) → Set
Exp V = ExpM V 0 
  
natToExp : ∀{M V} (s : NatSub) → Nohole s → (p : NatVar) → p ∈ₛ s → ExpM V M
natToExp Z Z here here = Z
natToExp (S n) (S n') here here = (S (natToExp n n' here here))
natToExp (S n) (S n') (there p) (there p') = natToExp n n' p p'
 
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

data _⇝R_ {m : ℕ} : Env m → Env m → Set where
  lift : {σ : Subs m}{e e' : ExpM 0 m} → e ↦R e' → (σ , e) ⇝R (σ , e')
  varZ : {σ : Subs m}{x : Fin m}{s : NatSub} → let s = lookup x σ in 
             {p : NatVar} → 
             s [ p ]:= just Z → 
             (σ , mvar x p) ⇝R (σ , Z)
  varS : {σ : Subs m}{x : Fin m}{s : NatSub} → let s = lookup x σ in 
             {p : NatVar} → 
             s [ p ]:= just (S unit) → 
             (σ , mvar x p) ⇝R (σ , S (mvar x (there p)))
  bind0 : {σ : Subs m}{x : Fin m} → let s = lookup x σ in 
           {p : NatVar} → s [ p ]:= nothing → 
          (σ , mvar x p) ⇝R (update x (updZ p) σ , Z) 
  bindS : {σ : Subs m}{x : Fin m} → let s = lookup x σ in 
    {p : NatVar} → s [ p ]:= nothing → 
    (σ , mvar x p) ⇝R (update x (updS p) σ , S (mvar x (there p)))

data _≤N_ : NatSub → NatSub → Set where
  ≤hole : {s : NatSub} → hole ≤N s 
  ≤Z : Z ≤N Z 
  ≤S : {s s' : NatSub} → s ≤N s' → S s ≤N S s'
  
----data _≤s_ : {m : ℕ} → Subs m → Subs m → Set where
----  ≤[] : _≤s_ [] []
----  ≤∷ : ∀{m s s'}{σ σ' : Subs m} → s ≤N s' → σ ≤s σ' → 
----                                        (s ∷ σ) ≤s (s' ∷ σ')
--  
_≤s_ : {m : ℕ} → Subs m → Subs m → Set
_≤s_ = VecI₂ _≤N_ 

≤N-refl : ∀{s} → s ≤N s
≤N-refl {hole} = ≤hole
≤N-refl {Z} = ≤Z
≤N-refl {S s} = ≤S ≤N-refl
                                        
≤N-trans : ∀{s s' s''} → s ≤N s' → s' ≤N s'' → s ≤N s''
≤N-trans ≤hole o' = ≤hole
≤N-trans ≤Z o' = o'
≤N-trans (≤S o) (≤S o') = ≤S (≤N-trans o o')

≤s-refl : ∀{m} {σ : Subs m} → σ ≤s σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤N-refl ∷ ≤s-refl

≤s-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤s σ' → σ' ≤s σ'' → σ ≤s σ''
≤s-trans [] [] = []
≤s-trans (s ∷ o) (s' ∷ o') = ≤N-trans s s' ∷ ≤s-trans o o' 

upd-point : ∀{m}{σ : Subs m}{f : NatSub → NatSub} (x : Fin m) → (lookup x σ ≤N f (lookup x σ)) → 
                   σ ≤s update x f σ
upd-point {σ = x ∷ σ} zero o = o ∷ ≤s-refl
upd-point {σ = s ∷ σ} (suc x) o = ≤N-refl ∷ upd-point x o 

updZ-mono : ∀{s}{p : NatVar} → s [ p ]:= nothing → s ≤N updZ p s
updZ-mono hereH = ≤hole
updZ-mono (thereH P) = ≤S (updZ-mono P)

updS-mono : ∀{s}{p : NatVar} → s [ p ]:= nothing → s ≤N updS p s
updS-mono hereH = ≤hole
updS-mono (thereH P) = ≤S (updS-mono P)

--embVar : ∀{V M}{σ σ' : Subs m}
                                        
⇝R-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} →   (σ , e) ⇝R (σ' , e') → σ ≤s σ'
⇝R-mono (lift x) = ≤s-refl
⇝R-mono (varZ x) = ≤s-refl
⇝R-mono (varS x) = ≤s-refl
⇝R-mono (bind0 {x = x} i) = upd-point x (updZ-mono i) 
⇝R-mono (bindS {x = x} i) = upd-point x (updS-mono i) 

suc-var : {p : NatVar}{s : NatSub} →  s [ p ]:= just (S unit) → p ∈ₛ s → there p ∈ₛ s
suc-var hereS here = there here
suc-var (thereS s₁) (there i) = there (suc-var s₁ i)

updS-var : {p : NatVar}{s : NatSub} →  s [ p ]:= nothing → p ∈ₛ s → there p ∈ₛ updS p s
updS-var hereH here = there here
updS-var (thereH o) (there i) = there (updS-var o i)

emb-var :  {p : NatVar}{s s' : NatSub} → s ≤N s' → p ∈ₛ s → p ∈ₛ s'
emb-var ≤hole here = here
emb-var ≤Z here = here
emb-var (≤S s₁) here = here
emb-var (≤S s₁) (there i) = there (emb-var s₁ i)

⇝R-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝R (σ' , e') → e ∈E σ → e' ∈E σ'
⇝R-in (lift x) e₁ = ↦R-in x e₁
⇝R-in (varZ x₁) e = Z
⇝R-in (varS x₁) (mvar x₂) = S (mvar (suc-var x₁ x₂))
⇝R-in (bind0 x₁) (mvar x₂) = Z
⇝R-in {σ = σ} (bindS x₁) (mvar {x = x} {p} x₂) = 
         S (mvar (subst (_∈ₛ_ (there p)) (upd-look x (updS p) σ) (updS-var x₁ x₂)))

getOrd : ∀{m}{σ σ' : Subs m} → σ ≤s σ' → (x : Fin m) → lookup x σ ≤N lookup x σ'
getOrd (x ∷ o) zero = x
getOrd (_ ∷ o) (suc x) = getOrd o x

emb-s : ∀{M}{p : NatVar}{σ σ' : Subs M} → σ ≤s σ' → (x : Fin M) → p ∈ₛ lookup x σ → p ∈ₛ lookup x σ' 
emb-s (x ∷ o) zero i = emb-var x i
emb-s (x ∷ o) (suc x₁) i = emb-s o x₁ i


emb-exp : ∀{v m}{σ σ' : Subs m}{e : ExpM v m} → σ ≤s σ' → e ∈E σ → e ∈E σ'
emb-exp o Z = Z
emb-exp o (S e₁) = S (emb-exp o e₁)
emb-exp o var = var
emb-exp o (mvar {x = x} x₁) = mvar (emb-s o x x₁)
emb-exp o (case e₁ alt₀ e₂ altₛ e₃) = case emb-exp o e₁ alt₀ emb-exp o e₂ altₛ emb-exp o e₃

--embCxt : ∀{m V}{M N : Subs m} → Cxt V M → M ≤s N → ExpM V N → ExpM V N
--embCxt hole o e = e
--embCxt (case H alt₀ e' altₛ e'') o e = case (embCxt H o e) alt₀ (embExp o e') altₛ embExp o e''
--
--repl : ∀{V m}(τ : Subs m) → (VecI Nohole τ) → ExpM V τ →  Exp V
--repl τ is (nat Z) = nat Z
--repl τ is (nat (S e)) = nat (S (repl τ is e))
--repl τ is (var x) = var x
--repl (a ∷ τ) (x ∷ is) (mvar zero p) = natToExp (a , x) p
--repl (a ∷ τ) (x ∷ is) (mvar (suc x₁) p) = repl τ is (mvar x₁ p)
--repl τ is (case e alt₀ e₁ altₛ e₂) = case repl τ is e alt₀ repl τ is e₁ altₛ repl τ is e₂

_⟪_,_,_⟫ : ∀{V M} → (e : ExpM V M) → (τ : Subs M) → (VecI Nohole τ) → e ∈E τ  → Exp V
Z ⟪ ns , is , Z ⟫ = Z
S e ⟪ ns , is , S o ⟫ = S (e ⟪ ns , is , o ⟫)
var x ⟪ ns , is , var ⟫ = var x
mvar zero p ⟪ a ∷ σ , x ∷ is , mvar x₁ ⟫ =  natToExp a x p x₁
mvar (suc x) p ⟪ a ∷ σ , x₁ ∷ is , mvar x₂ ⟫ = mvar x p ⟪ σ , is , mvar x₂ ⟫
(case e alt₀ e₁ altₛ e₂) ⟪ ns , is , case o alt₀ o₁ altₛ o₂ ⟫ =
      case e ⟪ ns , is , o ⟫ alt₀ e₁ ⟪ ns , is , o₁ ⟫ altₛ e₂ ⟪ ns , is , o₂ ⟫
--
data _⇝_ {m : ℕ} : Env m → Env m → Set where
  prom : {σ σ' : Subs m}{e e' : ExpM 0 m} → 
         (r : (σ , e) ⇝R (σ' , e')) → (H : Cxt 0 m)  → 
           (σ , H [/ e ]) ⇝ (σ' , H [/ e' ])
           
⇝-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝ (σ' , e') → σ ≤s σ'
⇝-mono (prom r H) = ⇝R-mono r

⇝-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝ (σ' , e') → e ∈E σ → e' ∈E σ'
⇝-in (prom r hole) o = ⇝R-in r o
⇝-in (prom r (case H alt₀ e'' altₛ e''')) (case o alt₀ o₁ altₛ o₂) = 
           case ⇝-in (prom r H) o alt₀ emb-exp (⇝R-mono r) o₁ altₛ emb-exp (⇝R-mono r) o₂

data _⇝*_ {m : ℕ} : Env m → Env m → Set where
  [] : {s : Env m} → s ⇝* s
  _∷_ : {s s' s'' : Env m} → (r : s ⇝ s') → (rs : s' ⇝* s'') → s ⇝* s''
  
⇝*-mono : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝* (σ' , e') → σ ≤s σ'
⇝*-mono [] = ≤s-refl
⇝*-mono (r ∷ rs) = ≤s-trans (⇝-mono r) (⇝*-mono rs)
  
⇝*-in : ∀{m}{σ σ' : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝* (σ' , e') → e ∈E σ → e' ∈E σ'
⇝*-in [] o = o
⇝*-in (r ∷ r₁) o = ⇝*-in r₁ (⇝-in r o)

data _⇝!_ {m : ℕ} : Env m → Env m → Set where
  fill : {σ τ : Subs m}{e : ExpM 0 m}{s : Env m} → VecI Nohole τ → (o : σ ≤s τ) →
       (r : s ⇝* (σ , e)) →  s ⇝! (τ ,  e)
       
inp! : ∀{m}{τ : Subs m} {e : ExpM 0 m}{s : Env m} → s ⇝! (τ , e) → VecI Nohole τ
inp! {s = proj₁ , proj₂} (fill x o x₁) = x

⇝!-mono : ∀{m}{σ τ : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝! (τ , e') → σ ≤s τ
⇝!-mono (fill x o r) = ≤s-trans (⇝*-mono r) o 

⇝!-in : ∀{m}{σ τ : Subs m}{e e' : ExpM 0 m} → (σ , e) ⇝! (τ , e') → e ∈E σ → e' ∈E τ
⇝!-in (fill x o r) i = emb-exp o (⇝*-in r i)


--emb-emp : ∀{V}{e : Exp V} → embExp [] e ≡ e
--emb-emp {e = nat Z} = refl
--emb-emp {e = nat (S e)} = cong (nat ∘ S) emb-emp
--emb-emp {e = var x} = refl
--emb-emp {e = mvar () p}
--emb-emp {e = case e alt₀ e₁ altₛ e₂} = 
--     cong₂ (λ x p → case x alt₀ proj₁ p altₛ proj₂ p) emb-emp (cong₂ _,_ emb-emp emb-emp)
--
--emb-equiv : ∀{m V}{σ τ : Subs m}{τ' : VecI Nohole τ} → (o : σ ≤s τ) → (e : ExpM V σ) →
--                   embExp o e ⟪ τ , τ' , ≤s-refl ⟫ ≡ e ⟪ τ , τ' , o ⟫ 
----emb-equiv {τ' = []} [] e = cong (λ e' → e' ⟪ [] , [] , [] ⟫) (emb-emp {e = e}) 
--emb-equiv o (nat Z) = refl
--emb-equiv o (nat (S e)) = cong (nat ∘ S) (emb-equiv o e)
--emb-equiv o (var x₁) = refl
--emb-equiv (x ∷ o) (mvar zero p) = {!x!}
--emb-equiv (x ∷ o) (mvar (suc x₁) p) = {!!}
--emb-equiv o (case e alt₀ e₁ altₛ e₂) = {!!}
--   
--⇝-sound : ∀{m}{σ τ : Subs m}{e : ExpM 0 σ}{e' : ExpM 0 τ} → 
--                        (r : (σ , e) ⇝! (τ , e')) → 
--            (e ⟪ τ , inp! r , ⇝!-mono r ⟫) ↦* (e' ⟪ τ , inp! r , ≤s-refl ⟫)
--⇝-sound (fill x o []) = {!!} 
--⇝-sound (fill x o (r ∷ rs)) = {!!}
