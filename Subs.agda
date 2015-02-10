module Subs where

open import FAlg 
open import PL
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import Data.Unit hiding (_≤_)
open import Data.Product 
open import Data.Vec hiding ([_])
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Data.Maybe

data EnvF : Alg → Set where
  val : {γ : Alg} → ValG EnvF γ → EnvF γ
  free : {γ : Alg} → EnvF γ 
  
fmapV : {t : Alg} {P Q : Alg → Set} → ({t' : Alg} → P t' → Q t') → ValG P t → ValG Q t
fmapV f V1 = V1
fmapV {t ⊗ u} f (a , b) = f a , f b
fmapV {t ⊕ u} f (inL a) = inL (f a)
fmapV {t ⊕ u} f (inR b) = inR (f b)

--data PosV : Alg → Alg → Set where
--   fst : ∀{t u} → PosV t (t ⊗ u) 
--   snd : ∀{t u} → PosV u (t ⊗ u) 
--   inL : ∀{t u} → PosV t (t ⊕ u) 
--   inR : ∀{t u} → PosV u (t ⊕ u) 
--   
--fmapP : {t : Alg} {P Q : Alg → Set} → ((t' : Alg) → (PosV t' t) → P t' → Q t') → ValG P t → ValG Q t
--fmapP f V1 = V1
--fmapP {t ⊗ u} f (a , b) = f t fst a , f u snd b
--fmapP {t ⊕ u} f (inL a) = inL (f t inL a)
--fmapP {t ⊕ u} f (inR b) = inR (f u inR b)
--   
--data ValP {P : Alg → Set} : {t u : Alg} → (PosV t u) → P t → ValG P u → Set where
--  fst : {t u : Alg}{a : P t}{b : P u} → ValP fst a ( a , b ) 
--  snd : {t u : Alg}{a : P t}{b : P u} → ValP snd b ( a , b ) 
--  inL : {t u : Alg}{a : P t} → ValP inL a (inL {u = u} a) 
--  inR : {t u : Alg}{a : P u} → ValP inR a (inR {t = t} a) 
--  --inR : 
--  
--fmapF : {t : Alg} {P Q : Alg → Set} → (b : ValG P t) →
--           ({t' : Alg}{p : PosV t' t} → (a : P t') → (ValP p a b) → Q t') → 
--             ValG Q t
--fmapF V1 f = V1
--fmapF (a , b) f = f a (fst {b = b}) , f b (snd {a = a})
--fmapF (inL a) f = inL (f a inL) 
--fmapF (inR b) f = inR (f b inR) 
--   
data VarF : {γ : Alg} → EnvF γ → Alg → Set where
  here : {t : Alg} {s : EnvF t} → VarF s t
  fst : {t γ γ' : Alg}{s : EnvF γ}{s' : EnvF γ'} (x : VarF s t) → VarF (val (s , s')) t
  snd : {t γ γ' : Alg}{s : EnvF γ}{s' : EnvF γ'} (x : VarF s' t) → VarF (val (s , s')) t
  inL : {t γ γ' : Alg}{s : EnvF γ} (x : VarF s t) → VarF (val (inL {u = γ'} s)) t
  inR : {t γ γ' : Alg}{s' : EnvF γ'} (x : VarF s' t) → VarF (val (inR {t = γ} s')) t
  
KUnit : {A : Set} → A → Set 
KUnit  x = Unit 

fmapMV : {t : Alg} {P Q : Alg → Set} → ({t' : Alg} → P t' → Q t') → 
         Maybe (ValG P t) → Maybe (ValG Q t)
fmapMV f (just x) = just (fmapV f x)
fmapMV f nothing = nothing

antCong : {A B : Alg → Set} → ({t' : Alg} → A t' → B t') → Set 
antCong {A}{B} f = {t : Alg} → {a b : A t} → f a ≡ f b → a ≡ b

simCong : {A B : Set} → (A  → B ) → Set 
simCong {A}{B} f = {a b : A} → f a ≡ f b → a ≡ b

justCong : {A : Set} → simCong {A = A} {B = Maybe A} just
justCong refl = refl

congInL : ∀ {u t} {A : Alg → Set} → simCong {A = A u} {B = ValG A (u ⊕ t)} inL
congInL refl = refl

congInR : ∀ {u t} {A : Alg → Set} → simCong {A = A t} {B = ValG A (u ⊕ t)} inR
congInR refl = refl


id : {A : Set} → A → A
id x = x

fmapMVuniq : {t : Alg} {P Q : Alg → Set} → (f : {t' : Alg} → P t' → Q t') → antCong {A = P} f → 
          {a b : Maybe (ValG P t)} → fmapMV f a ≡ fmapMV f b → a ≡ b
fmapMVuniq f a {just V1} {just V1} r = refl
fmapMVuniq f a {just (a₁ , b)} {just (a₂ , b₁)} r =   
     cong₂ (λ x x₁ → just (x , x₁)) (a (cong fstV (justCong r))) (a (cong sndV (justCong r)))
fmapMVuniq f a {just (inL a₁)} {just (inL a₂)} r = 
           cong (λ x → just (inL x)) (a (congInL (justCong r)))
        --   cong (λ x → just (inL x)) (subst {!!} r a)
fmapMVuniq f a {just (inL a₁)} {just (inR b)} ()
fmapMVuniq f a {just (inR b)} {just (inL a₁)} ()
fmapMVuniq f a {just (inR b)} {just (inR b₁)} r = 
             cong (λ x → just (inR x)) (a (congInR (justCong r)))
fmapMVuniq f a {just x} {nothing} ()
fmapMVuniq f a {nothing} {just x} ()
fmapMVuniq f a {nothing} {nothing} refl = refl

fstUniq : ∀{u t}{s : EnvF t}{s' : EnvF  u} → antCong {A = λ x → VarF s x} {B = λ x → VarF (val (s , s')) x } fst
fstUniq refl = refl


data _[_]:=_ : {γ t : Alg} (s : EnvF γ) → VarF s t → Maybe (ValG (VarF s) t) → Set where
  hereV : val V1 [ here ]:= just V1 
  hereP : ∀{γ γ'}{s : EnvF γ}{s' : EnvF γ'} → val (s , s') [ here ]:= just (fst here , snd here )
  hereL : ∀{γ γ'}{s : EnvF γ} → val (inL {u = γ'} s) [ here ]:= just (inL (inL here) )
  hereR : ∀{γ γ'}{s' : EnvF γ'} → val (inR {t = γ} s') [ here ]:= just (inR (inR here) )

  nothere : ∀{γ} → free [ here {t = γ} ]:= nothing

  fst : ∀{γ γ' t}{s : EnvF γ}{s' : EnvF γ'}{x : VarF s t}{a : Maybe (ValG (VarF s) t)} → 
           (s [ x ]:= a) → val (s , s') [ fst x ]:= fmapMV fst a
  snd : ∀{γ γ' t}{s : EnvF γ}{s' : EnvF γ'}{x : VarF s' t}{a : Maybe (ValG (VarF s') t)} → 
           (s' [ x ]:= a) → val (s , s') [ snd x ]:= fmapMV snd a
  inL : ∀{γ γ' t}{s : EnvF γ}{x : VarF s t}{a : Maybe (ValG (VarF s) t)} → 
           (s [ x ]:= a) → val (inL {u = γ'} s) [ inL x ]:= fmapMV inL a
  inR : ∀{γ γ' t}{s' : EnvF γ'}{x : VarF s' t}{a : Maybe (ValG (VarF s') t)} → 
           (s' [ x ]:= a) → val (inR {t = γ} s') [ inR x ]:= fmapMV inR a
           
fromfst : ∀{γ γ' t}{s : EnvF γ}{s' : EnvF γ'}{x : VarF s t}{b : Maybe (ValG (VarF (val (s , s'))) t )}{a : Maybe (ValG (VarF s) t)} → 
           val (s , s') [ fst x ]:= b → (b ≡ fmapMV fst a) → (s [ x ]:= a)  
fromfst (fst a₂) b with fmapMVuniq fst fstUniq b 
fromfst (fst a₂) b | refl = a₂

           
inExist : ∀ {γ t} → (s : EnvF γ) → (x : VarF s t) → ∃ (_[_]:=_ s x)
inExist (val V1) here = just V1 , hereV
inExist (val (a , b)) here = just (fst here , snd here) , hereP
inExist (val (a , b)) (fst x₁) with inExist a x₁
inExist (val (a , b)) (fst x₁) | proj₁ , proj₂ = fmapMV fst proj₁ , fst proj₂
inExist (val (a , b)) (snd x₁) with inExist b x₁ 
inExist (val (a , b)) (snd x₁) | proj₁ , proj₂ = fmapMV snd proj₁ , snd proj₂
inExist (val (inL a)) here = just (inL (inL here)) , hereL
inExist (val (inL a)) (inL x₁) with inExist a x₁
inExist (val (inL a)) (inL x₁) | proj₁ , proj₂ = fmapMV inL proj₁ , inL proj₂
inExist (val (inR b)) here = just (inR (inR here)) , hereR
inExist (val (inR b)) (inR x₁) with inExist b x₁ 
inExist (val (inR b)) (inR x₁) | proj₁ , proj₂ = fmapMV inR proj₁ , inR proj₂
inExist free here = nothing , nothere

inUniq : ∀{γ t} {s : EnvF γ}{x : VarF s t} {a b : Maybe (ValG (VarF s) t)} → s [ x ]:= a → s [ x ]:= b → a ≡ b 
inUniq hereV hereV = refl
inUniq hereP hereP = refl
inUniq hereL hereL = refl
inUniq hereR hereR = refl
inUniq nothere nothere = refl
inUniq (fst p1) (fst p2) = cong  (fmapMV fst) (inUniq p1 p2)
inUniq (snd p1) (snd p2) = cong (fmapMV snd) (inUniq p1 p2)
inUniq (inL p1) (inL p2) = cong (fmapMV inL) (inUniq p1 p2)
inUniq (inR p1) (inR p2) = cong (fmapMV inR) (inUniq p1 p2)
                   
--onF : {t t' : Alg} {P : Alg → Set}{a : P t'}(b : ValG P t) → 
--  {p : PosV t' t} → ValP p a b → (P t' → P t')  →  ValG P t
--onF V1 () f
--onF (a , b) fst f = f a , b
--onF (a , b) snd f = a , f b
--onF (inL a) inL f = inL (f a)
--onF (inR b) inR f = inR (f b)

--nin : {t γ : Alg} → (s : EnvF γ) → VarF s t → Set
--nin {t} s x  = ¬ (Σ (ValG (VarF s) t) (_[_]:=_ s x ))

liftn : {A B : Set}{F : A → Set}{G : B → A}  →  (Σ A F  → Σ B (λ a → F (G a)))
  → ¬ (Σ B (λ a → F (G a))) → ¬ (Σ A F)
liftn g a (proj₁ , proj₂) = a (g (proj₁ , proj₂))

cont : {A : Set} → ⊥ → A
cont ()
--
insert : {γ t : Alg} (s : EnvF γ) → (x : VarF s t) →
         ValG KUnit t → s [ x ]:= nothing → Σ (EnvF γ) (λ s → ValG (VarF s) t)
insert (val V1) here a ()
insert (val (a , b)) here a₁ ()
insert (val (a , b)) (fst x₁) a₁ n with insert a x₁ a₁ (fromfst n refl)
insert (val (a , b)) (fst x₁) a₁ n | proj₁ , proj₂ = val (proj₁ , b) , fmapV fst proj₂
insert (val (a , b)) (snd x₁) a₁ n = {!!}
insert (val (inL a)) here a₁ ()
insert (val (inL a)) (inL x₁) a₁ n = {!!}
insert (val (inR b)) here a ()
insert (val (inR b)) (inR x₁) a n = {!!}
insert free here V1 n = free , V1
insert free here (a , b) n = val (free , free) , fst here , snd here
insert free here (inL a) n = val (inL free) , inL (inL here)
insert free here (inR b) n = val (inR free) , inR (inR here)
--insert (val s) here a = val a , fmapF a (λ _ x → there x here)
--insert (val s') (there {a = s} x p) a with insert s p a 
--insert (val s') (there {p = pos} x p) a | proj₁ , proj₂ = 
--  val (onF s' x (λ _ → proj₁)) , fmapF proj₂ (λ a₁ x₁ → there {!!} a₁)
--insert free x a = {!!}
----insert (val x) here a = val a
----insert (val x) (there {a = a} x₁ x₂) a₁ 
----  = val (onF x x₁ (λ z → insert a x₂ a₁))
----insert free here a = val a
--
--data _<=_ : {γ : Alg} → EnvF γ → EnvF γ → Set where
--  ref : {γ : Alg} {a : EnvF γ} → a <= a 
--  free : {γ : Alg} {a : EnvF γ} → free <= a 
--  pair : {γ δ : Alg} {a a' : EnvF γ}{b b' : EnvF δ} → 
--    a <= a' → b <= b' → val (a , b) <= val (a' , b')
--  inL :  {γ δ : Alg} {a a'  : EnvF γ} → a <= a' → val (inL {u = δ} a) <= val (inL a')
--  inR :  {γ δ : Alg} {a a'  : EnvF γ} → a <= a' → val (inR {t = δ} a) <= val (inR a')
--  
--embVarF : {γ t : Alg} {s s' : EnvF γ} → s <= s' → VarF s t →  VarF s' t
--embVarF o here          = here
--embVarF ref (there fst v)  = there fst v
--embVarF (pair o _) (there fst v)  = there fst (embVarF o v)
--embVarF ref (there snd v) = there snd v
--embVarF (pair _ o₁)(there snd v) = there snd (embVarF o₁ v)
--embVarF ref (there inL v) = there inL v
--embVarF (inL o) (there inL v) = there inL (embVarF o v) 
--embVarF ref (there inR v)  = there inR v
--embVarF (inR o) (there inR v) = there inR (embVarF o v) 

