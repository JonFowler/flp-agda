module Exp where

open import Data.Nat
open import Data.Fin
open import Subs
open import VecI
open import Data.Vec
open import Relation.Binary.PropositionalEquality

data Exp {m : ℕ} (V : ℕ) (M : Subs m) : Set where
  val : Val (Exp V M) → Exp V M
  var : Fin V → Exp V M
  mvar : (x : Fin m) → (p : Holes (lookup x M))  → Exp V M 
  case_alt₀_altₛ_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  

--toExp : ∀{m}{s} → (p : Holes s) → (b : Binding s) → Val  
--toExp {M = M} x p b = {!!}
