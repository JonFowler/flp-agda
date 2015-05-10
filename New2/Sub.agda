module Sub where

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import VecI
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Nat (A : Set) : Set where
  Z : Nat A
  S : A → Nat A
 
data Sub : Set where
  hole : Sub
  Z : Sub
  S : Sub → Sub
 
Subs : ℕ → Set
Subs = Vec Sub
  
data Pos : Set where
  here : Pos
  there : Pos → Pos
  
data _∈ₛ_ : Pos → Sub → Set where
  here : here ∈ₛ hole 
  there : ∀{p s} → p ∈ₛ s → there p ∈ₛ S s 
  
_+ₚ_ : Pos → Pos → Pos
here +ₚ p = p
there p +ₚ p' = there (p +ₚ p')



Inp : Sub → Set
Inp hole = ⊥
Inp Z = Unit
Inp (S s) = Inp s


data _≤ₛ_ : Sub → Sub → Set where
  ≤ₛ-hole : ∀{s} → hole ≤ₛ s 
  ≤ₛ-Z : Z ≤ₛ Z 
  ≤ₛ-S : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'

_≤_ : {m : ℕ} → Subs m → Subs m → Set
_≤_ = VecI₂ _≤ₛ_ 

≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤ₛ-hole 
≤ₛ-refl {Z} = ≤ₛ-Z 
≤ₛ-refl {S s} = ≤ₛ-S ≤ₛ-refl 


≤ₛ-trans : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
≤ₛ-trans ≤ₛ-hole o' = ≤ₛ-hole
≤ₛ-trans ≤ₛ-Z ≤ₛ-Z = ≤ₛ-Z
≤ₛ-trans (≤ₛ-S o) (≤ₛ-S o') = ≤ₛ-S (≤ₛ-trans o o')

≤-refl : ∀{m} {σ : Subs m} → σ ≤ σ
≤-refl {σ = []} = []
≤-refl {σ = x ∷ σ} = ≤ₛ-refl {x} ∷ ≤-refl

≤-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤ σ' → σ' ≤ σ'' → σ ≤ σ''
≤-trans [] [] = []
≤-trans {suc m}{s ∷ _}{s' ∷ _} (o ∷ os) (o' ∷ os') = ≤ₛ-trans {s}{s'} o o' ∷ ≤-trans os os' 



updateS : Sub → Pos → Sub → Sub
updateS s here s' = s 
updateS s (there p) (S n) = S (updateS s p n)
updateS s (there p) a  = hole

lookupS : Pos → Sub → Sub
lookupS here s = s
lookupS (there p) (S s) = lookupS p s
lookupS (there p) s = hole


--∈-lookupS : ∀{p s} → p ∈ₛ s → hole ≡ lookupS p s → p ∈ₛ s
--∈-lookupS {here} {hole} x = unit
--∈-lookupS {here} {Z} ()
--∈-lookupS {here} {S s} ()
--∈-lookupS {there p} {hole} x = {!x!}
--∈-lookupS {there p} {Z} x = {!!}
--∈-lookupS {there p} {S s} x = {!!}

outS : Sub → Sub
outS hole = hole
outS Z = Z
outS (S s) = s

there-lookupS : ∀{s s'}(p : Pos) → S s' ≡ lookupS p s → s' ≡ lookupS (there p) s
there-lookupS {hole} (here)  ()
there-lookupS {Z}   (here) () 
there-lookupS {S s} (here)  eq = cong outS eq
there-lookupS {hole} (there p)  ()
there-lookupS {Z} (there p) ()
there-lookupS {S s} (there p) eq = there-lookupS p eq 

lookupS-mono : ∀{s s'} → (p : Pos) → s ≤ₛ s' → lookupS p s ≤ₛ lookupS p s'
lookupS-mono here o = o
lookupS-mono (there p) ≤ₛ-hole = ≤ₛ-hole
lookupS-mono (there p) ≤ₛ-Z = ≤ₛ-hole
lookupS-mono (there p) (≤ₛ-S o) = lookupS-mono p o





data ValPos : Set where
  hole : Pos → ValPos
  Z : ValPos
  S : ValPos → ValPos
  

