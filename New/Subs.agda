module Subs where

open import VecI
open import Helpful
open import Data.Vec
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty

data Sub : Set where
  Z : Sub
  S : Sub → Sub
  hole : Sub
  
Subs : ℕ → Set
Subs = Vec Sub
  
data SubVar : Sub → Set where
  hole : SubVar hole
  inS : {s : Sub} → SubVar s → SubVar (S s)
  
data _≤ₛ_ : Sub → Sub → Set where
  ≤hole : ∀{s} → hole ≤ₛ s
  ≤Z : Z ≤ₛ Z 
  ≤inS : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'
  
SubVars : ∀{M} → Subs M → Set
SubVars = VecI SubVar 

_≤s_ : ∀{M} → Subs M → Subs M → Set
_≤s_ = VecI₂ _≤ₛ_

-- Ordering is reflexive
≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤hole
≤ₛ-refl {Z} = ≤Z
≤ₛ-refl {S s} = ≤inS ≤ₛ-refl
                                        
-- Transitivity (composability) of ordering
_≤ₛ∘_ : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
_≤ₛ∘_ ≤hole o' = ≤hole
_≤ₛ∘_ ≤Z o' = o'
_≤ₛ∘_ (≤inS o) (≤inS o') = ≤inS (o ≤ₛ∘ o')

-- Lifting reflectivity to environment order
≤s-refl : ∀{m} {σ : Subs m} → σ ≤s σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤ₛ-refl ∷ ≤s-refl

-- Lifting transivity to environment order
_≤s∘_ : ∀{m} {σ σ' σ'' : Subs m} → σ ≤s σ' → σ' ≤s σ'' → σ ≤s σ''
_≤s∘_ [] [] = []
_≤s∘_ (s ∷ o) (s' ∷ o') = s ≤ₛ∘ s' ∷ o ≤s∘ o' 

--data Bind : Sub → Sub → Set where
--  bindZ : Bind hole Z
--  bindS : Bind hole (S hole) 
--  inS : ∀{s s'} → Bind s s' → Bind (S s) (S s')

_<ₛ_ : Sub → Sub → Set
s <ₛ s' = s ≤ₛ s' × s ≠ s'

Minimal : {A : Set} → (ord : A → A → Set) → (P : A → Set) → (x : A) →  Set
Minimal {A} ord P x = (y : A) → (P y) → ord y x → x ≡ y
  
Bind : Sub → Set
Bind s = Σ Sub (Minimal _≤ₛ_ (_<ₛ_ s))
  
