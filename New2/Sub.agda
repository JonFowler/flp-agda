module Sub where

open import Data.Unit
open import Data.Empty
open import Data.Nat
open import Data.Fin
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
  
_∈ₛ_ : Pos → Sub → Set
here ∈ₛ hole = Unit
there p ∈ₛ S s = p ∈ₛ s
_ ∈ₛ _ = ⊥

Inp : Sub → Set
Inp hole = ⊥
Inp Z = Unit
Inp (S s) = Inp s


data _≤ₛ_ : Sub → Sub → Set where
  ≤ₛ-hole : ∀{s} → hole ≤ₛ s 
  ≤ₛ-Z : Z ≤ₛ Z 
  ≤ₛ-S : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'

_≤s_ : {m : ℕ} → Subs m → Subs m → Set
_≤s_ = VecI₂ _≤ₛ_ 

≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤ₛ-hole 
≤ₛ-refl {Z} = ≤ₛ-Z 
≤ₛ-refl {S s} = ≤ₛ-S ≤ₛ-refl 


≤ₛ-trans : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
≤ₛ-trans ≤ₛ-hole o' = ≤ₛ-hole
≤ₛ-trans ≤ₛ-Z ≤ₛ-Z = ≤ₛ-Z
≤ₛ-trans (≤ₛ-S o) (≤ₛ-S o') = ≤ₛ-S (≤ₛ-trans o o')

≤s-refl : ∀{m} {σ : Subs m} → σ ≤s σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤ₛ-refl {x} ∷ ≤s-refl

≤s-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤s σ' → σ' ≤s σ'' → σ ≤s σ''
≤s-trans [] [] = []
≤s-trans {suc m}{s ∷ _}{s' ∷ _} (o ∷ os) (o' ∷ os') = ≤ₛ-trans {s}{s'} o o' ∷ ≤s-trans os os' 



updateS : Sub → Pos → Sub → Sub
updateS s here s' = s 
updateS s (there p) (S n) = S (updateS s p n)
updateS s (there p) a  = hole

lookupS : Pos → Sub → Sub
lookupS here s = s
lookupS (there p) (S s) = lookupS p s
lookupS (there p) s = hole

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
