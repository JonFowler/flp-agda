module Sub where

open import Data.Product hiding (zip)
open import Data.Vec as V
open import Data.Maybe as M
open import Data.Fin hiding (_+_ ) hiding (lift)
open import Data.Nat 
open import Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import VecI

data Nat (A : Set) : Set where
  Z : Nat A
  S : A → Nat A
  
 
mapNat : {A B : Set} → (A → B) → Nat A → Nat B
mapNat f Z = Z
mapNat f (S x) =  S (f x) 
 

data Sub : Set where
  hole : Sub
  Z : Sub
  S : Sub → Sub
  
Subs : ℕ → Set
Subs = Vec Sub 
 
data Nohole : Sub → Set where
  Z : Nohole Z
  S : {n : Sub} → Nohole n → Nohole (S n)
  
Noholes : ∀{M} → Subs M → Set
Noholes σ = VecI Nohole σ
  
Input : Set
Input = Σ Sub Nohole
  
Inputs : ℕ → Set
Inputs m = Vec Input m
  
data SubVar : Set where
  here : SubVar 
  there : (p : SubVar) → SubVar 
  
data _∈ₛ_ : SubVar → Sub → Set where
  here : ∀{s} → here ∈ₛ s
  there : ∀{p s} → p ∈ₛ s → there p ∈ₛ S s
  
updZ : SubVar → Sub → Sub
updZ here s = Z 
updZ (there p) (S n) = S (updZ p n)
updZ  _ _ = Z

updS :  SubVar → Sub → Sub 
updS here s = S hole 
updS (there p) (S n) = S (updS p n)
updS _  _ = Z 

data _[_]:=_ : (s : Sub) → SubVar → Maybe (Nat Unit) → Set where 
  hereZ : Z [ here ]:= just Z 
  hereS : {a : Sub} → S a [ here ]:= just (S unit) 
  hereH : hole [ here ]:= nothing
  thereZ : {s : Sub}{p : SubVar} → s [ p ]:=  just Z → S s [ there p ]:= just Z 
  thereS : {s : Sub}{p  : SubVar} → s [ p ]:=  just (S unit) → 
                S s [ there p ]:= just (S unit) 
  thereH : {s : Sub}{p : SubVar} → s [ p ]:= nothing → S s [ there p ]:= nothing

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

updZ-mono : ∀{s}{p : SubVar} → s [ p ]:= nothing → s ≤ₛ updZ p s
updZ-mono hereH = ≤hole
updZ-mono (thereH P) = ≤S (updZ-mono P)

updS-mono : ∀{s}{p : SubVar} → s [ p ]:= nothing → s ≤ₛ updS p s
updS-mono hereH = ≤hole
updS-mono (thereH P) = ≤S (updS-mono P)

≤ₛ-trans-refl : {s s' : Sub}{o : s ≤ₛ s'} → o ≡ ≤ₛ-trans ≤ₛ-refl o
≤ₛ-trans-refl {o = ≤hole} = refl
≤ₛ-trans-refl {o = ≤Z} = refl
≤ₛ-trans-refl {o = ≤S o} = cong ≤S ≤ₛ-trans-refl

≤s-trans-refl : ∀{m}{σ σ' : Subs m}{o : σ ≤s σ'} → o ≡ ≤s-trans ≤s-refl o 
≤s-trans-refl {o = []} = refl
≤s-trans-refl {o = x ∷ o} = cong₂ _∷_ ≤ₛ-trans-refl ≤s-trans-refl 


suc-var : {p : SubVar}{s : Sub} →  s [ p ]:= just (S unit) → p ∈ₛ s → there p ∈ₛ s
suc-var hereS here = there here
suc-var (thereS s₁) (there i) = there (suc-var s₁ i)

updS-var : {p : SubVar}{s : Sub} →  s [ p ]:= nothing → p ∈ₛ s → there p ∈ₛ updS p s
updS-var hereH here = there here
updS-var (thereH o) (there i) = there (updS-var o i)

emb-var :  {p : SubVar}{s s' : Sub} → s ≤ₛ s' → p ∈ₛ s → p ∈ₛ s'
emb-var ≤hole here = here
emb-var ≤Z here = here
emb-var (≤S s₁) here = here
emb-var (≤S s₁) (there i) = there (emb-var s₁ i)



