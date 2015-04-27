module Exp where

open import Data.Nat
open import Data.Fin
open import Subs
open import VecI
open import Data.Vec
open import Relation.Binary.PropositionalEquality
open import Function

data Exp {m : ℕ} (V : ℕ) (M : Subs m) : Set where
  Z : Exp V M
  S : Exp V M → Exp V M
  var : Fin V → Exp V M
  mvar : (x : Fin m) → (p : Holes (lookup x M))  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  
conv : ∀{m V}{M : Subs m}(x : Fin m) → (p : Holes (lookup x M)) → 
     (b : Bindings M) → Exp V (zipWithI updateSub M b) 
conv {M = x ∷ M} zero p (b ∷ bs) with b p | inspect b p
conv {._} {V} {m ∷ M} zero p (b ∷ bs) | Z | eq = Z
conv {._} {V} {m ∷ M} zero p (b ∷ bs) | S s | eq = 
    let r = conv {V = V} zero (inS p) (b ∘ outS ∷ bs) in S {!!}
conv {._} {V} {x ∷ M} zero p (b ∷ bs) | hole | Reveal_is_.[ eq ] =  
  mvar zero (embedHole b p (sym eq))
conv {M = x ∷ M} (suc x₁) p b = {!!}

conv' : ∀{m V}{M M' : Subs m}(x : Fin m) → (p : Holes (lookup x M)) → (M ≤s M') → Exp V M' 
conv' {M = hole ∷ ms} zero p (≤hole s ∷ b₁) = {!p!}
conv' zero p (≤Z ∷ b₁) = {!!}
conv' zero p (≤inS x ∷ b₁) = {!!}
conv' (suc x) p b = {!!}



