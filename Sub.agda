module Sub where

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

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
        (f : A → B → C → D) {x y u v m n} → x ≡ y → u ≡ v → m ≡ n → f x u m ≡ f y v n
cong₃ f refl refl refl = refl

subst₃ : ∀ {A B C : Set}(P : A → B → C → Set)
         {x₁ x₂ y₁ y₂ z₁ z₂} → x₁ ≡ x₂ → y₁ ≡ y₂ → z₁ ≡ z₂ → P x₁ y₁ z₁ → P x₂ y₂ z₂
subst₃ P refl refl refl a = a

data Sub : Set where
  hole : Sub
  Z : Sub
  S : Sub → Sub
  
Subs : ℕ → Set
Subs = Vec Sub 
 
data Inp : Sub → Set where
  Z : Inp Z
  S : {n : Sub} → Inp n → Inp (S n)
  
Inps : ∀{M} → Subs M → Set
Inps σ = VecI Inp σ
  
data SubVar : Set where
  here : SubVar 
  there : (p : SubVar) → SubVar 
  
data _∈ₛ_ : SubVar → Sub → Set where
  here : ∀{s} → here ∈ₛ s
  there : ∀{p s} → p ∈ₛ s → there p ∈ₛ S s
  
∈ₛ-uniq : ∀{p s} → (i1 : p ∈ₛ s) → (i2 : p ∈ₛ s) → i1 ≡ i2
∈ₛ-uniq here here = refl
∈ₛ-uniq (there i1) (there i2) = cong there (∈ₛ-uniq i1 i2)
  
updateS : Sub → SubVar → Sub → Sub
updateS s here s' = s 
updateS s (there p) (S n) = S (updateS s p n)
updateS s (there p) a  = hole

data _[_]:=_ : (s : Sub) → SubVar → Sub → Set where 
  here : {s : Sub} → s [ here ]:= s 
  there : {s s' : Sub}{p : SubVar} → s [ p ]:= s' → S s [ there p ]:= s'

data _≤ₛ_ : Sub → Sub → Set where
  ≤hole : {s : Sub} → hole ≤ₛ s 
  ≤Z : Z ≤ₛ Z 
  ≤S : {s s' : Sub} → s ≤ₛ s' → S s ≤ₛ S s'
  
----data _≤s_ : {m : ℕ} → Subs m → Subs m → Set where
----  ≤[] : _≤s_ [] []
----  ≤∷ : ∀{m s s'}{σ σ' : Subs m} → s ≤N s' → σ ≤s σ' → 
----                                        (s ∷ σ) ≤s (s' ∷ σ')
--  
_≤s_ : {m : ℕ} → Subs m → Subs m → Set
_≤s_ = VecI₂ _≤ₛ_ 

≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤hole
≤ₛ-refl {Z} = ≤Z
≤ₛ-refl {S s} = ≤S ≤ₛ-refl
                                        
≤ₛ-trans : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
≤ₛ-trans ≤hole o' = ≤hole
≤ₛ-trans ≤Z o' = o'
≤ₛ-trans (≤S o) (≤S o') = ≤S (≤ₛ-trans o o')

≤s-refl : ∀{m} {σ : Subs m} → σ ≤s σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤ₛ-refl ∷ ≤s-refl

≤s-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤s σ' → σ' ≤s σ'' → σ ≤s σ''
≤s-trans [] [] = []
≤s-trans (s ∷ o) (s' ∷ o') = ≤ₛ-trans s s' ∷ ≤s-trans o o' 

upd-point : ∀{m}{σ : Subs m}{f : Sub → Sub} (x : Fin m) → (lookup x σ ≤ₛ f (lookup x σ)) → 
                   σ ≤s update x f σ
upd-point {σ = x ∷ σ} zero o = o ∷ ≤s-refl
upd-point {σ = s ∷ σ} (suc x) o = ≤ₛ-refl ∷ upd-point x o 

≤s-upd : ∀{m}{σ τ : Subs m}{f : Sub → Sub} (x : Fin m) → (f (lookup x σ) ≤ₛ (lookup x τ)) → σ ≤s τ →
                   update x f σ ≤s τ 
≤s-upd zero s (x ∷ o) = s ∷ o
≤s-upd (suc x) s (x₁ ∷ o) = x₁ ∷ ≤s-upd x s o

upd-mono : ∀{s s'}{p : SubVar} → s [ p ]:= hole → s ≤ₛ updateS s' p s
upd-mono here = ≤hole
upd-mono (there a) = ≤S (upd-mono a)

updateS-point : ∀{r s s'}(p : SubVar) → (s ≤ₛ s') → updateS s p r ≤ₛ updateS s' p r
updateS-point here o = o
updateS-point {hole} (there p) o = ≤hole
updateS-point {Z} (there p) o = ≤hole
updateS-point {S r} (there p) o = ≤S (updateS-point p o)


≤ₛ-trans-refl : {s s' : Sub}{o : s ≤ₛ s'} → o ≡ ≤ₛ-trans ≤ₛ-refl o
≤ₛ-trans-refl {o = ≤hole} = refl
≤ₛ-trans-refl {o = ≤Z} = refl
≤ₛ-trans-refl {o = ≤S o} = cong ≤S ≤ₛ-trans-refl

≤s-trans-refl : ∀{m}{σ σ' : Subs m}{o : σ ≤s σ'} → o ≡ ≤s-trans ≤s-refl o 
≤s-trans-refl {o = []} = refl
≤s-trans-refl {o = x ∷ o} = cong₂ _∷_ ≤ₛ-trans-refl ≤s-trans-refl 


--suc-var : {p : SubVar}{s : Sub} →  s [ p ]:= just (S unit) → p ∈ₛ s → there p ∈ₛ s
--suc-var hereS here = there here
--suc-var (thereS s₁) (there i) = there (suc-var s₁ i)
--
updS-var : {s' : Sub}{p : SubVar}{s : Sub} → p ∈ₛ s →  updateS s' p s [ p ]:= s'
updS-var here = here
updS-var (there i) = there (updS-var i)

emb-var :  {p : SubVar}{s s' : Sub} → s ≤ₛ s' → p ∈ₛ s → p ∈ₛ s'
emb-var ≤hole here = here
emb-var ≤Z here = here
emb-var (≤S s₁) here = here
emb-var (≤S s₁) (there i) = there (emb-var s₁ i)

getSub : (p : SubVar) → (s : Sub) → Sub
getSub here s = s
getSub (there p) hole = hole
getSub (there p) Z = hole 
getSub (there p) (S s) = getSub p s

≤ₛ-upd : ∀{s s'} → (p : SubVar) → s ≤ₛ s' → updateS (getSub p s') p s ≤ₛ s'
≤ₛ-upd here o = ≤ₛ-refl
≤ₛ-upd (there p) ≤hole = ≤hole
≤ₛ-upd (there p) ≤Z = ≤hole
≤ₛ-upd (there p) (≤S o) = ≤S (≤ₛ-upd p o)

getSub-upd : ∀ {s' p s} → (p ∈ₛ s') → s ≡ getSub p (updateS s p s')
getSub-upd here = refl
getSub-upd (there i) = getSub-upd i

getSub-there : ∀ {p s s'} → S s' ≡ getSub p s → s' ≡ getSub (there p) s
getSub-there {here} {hole} ()
getSub-there {here} {Z} ()
getSub-there {here} {S s'} refl = refl
getSub-there {there p} {hole} ()
getSub-there {there p} {Z} ()
getSub-there {there p} {S s} eq = getSub-there {p} {s} eq

getSub-in : ∀{p s} → (p ∈ₛ s) → s [ p ]:= getSub p s
getSub-in here = here
getSub-in (there i) = there (getSub-in i)

getSub-mono : ∀ {s s'} → (p : SubVar) → s ≤ₛ s' → getSub p s ≤ₛ getSub p s'
getSub-mono here o = o
getSub-mono (there p) ≤hole = ≤hole
getSub-mono (there p) ≤Z = ≤hole
getSub-mono (there p) (≤S o) = getSub-mono p o

getSub-eq : ∀{p s s'} → s [ p ]:= s' → s' ≡ getSub p s
getSub-eq here = refl
getSub-eq (there p) = getSub-eq p 

look-in : ∀{p s s'} → s [ p ]:= s' → (p ∈ₛ s)
look-in here = here
look-in (there i) = there (look-in i)

look-S : ∀{p s s'} → s [ p ]:= S s' → s [ there p ]:= s' 
look-S here = there here
look-S (there i) = there (look-S i)

look-there : ∀{p s s'} → s [ there p ]:= s' → s [ p ]:= S s' 
look-there (there here) = here
look-there (there (there i)) = there (look-there (there i)) 



