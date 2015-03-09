module num where

open import Data.Sum
open import Data.Container
open import Data.Maybe
open import Data.Product
open import Data.Fin hiding (_+_)
open import Data.Nat 
open import Relation.Binary.PropositionalEquality


data Val (A : Set) : Set where
  Z : Val A
  S : A → Val A
  
data Exp (V M : ℕ) : Set where
  val : Val (Exp V M) → Exp V M
  var : Fin V → Exp V M
  mvar : Fin M → Exp V M 
  case_of_#_ : Exp V M → Exp V M → Exp (suc V) M → Exp V M
  
sucVar : {V' : ℕ}(V : ℕ) → Fin (V + V') → Fin (V + suc V')
sucVar zero n = suc n
sucVar (suc V) zero = zero
sucVar (suc V) (suc n) = suc (sucVar V n)
  
sucExp : {V' M : ℕ}(V : ℕ) → Exp (V + V') M → Exp (V + suc V') M
sucExp V (val Z) = val Z
sucExp V (val (S x)) = val (S (sucExp V x))
sucExp V (var x) = var (sucVar V x) 
sucExp V (mvar x) = mvar x
sucExp V (case e of e₁ # e₂) = case (sucExp V e) of (sucExp V e₁) # sucExp (suc V) e₂

sub : {V' M : ℕ} (V : ℕ) → Exp (V + suc V') M → Exp V' M → Exp (V + V') M
sub V (val Z) ef = val Z
sub V (val (S x)) ef = val (S (sub V x ef))
sub zero (var zero) ef = ef
sub zero (var (suc x)) ef = var x
sub (suc V) (var zero) ef = var zero
sub (suc V) (var (suc x)) ef with sub V (var x) ef
... | e' = sucExp 0 e'
sub V (mvar x) ef = mvar x
sub V (case e of e₁ # e₂) ef = case sub V e ef of sub V e₁ ef # sub (suc V) e₂ ef
  
_[-_-] : {V M : ℕ} → Exp (suc V) M → Exp V M → Exp V M
_[-_-] = sub 0
  
data _↦R_ {M : ℕ} : Exp 0 M → Exp 0 M → Set where
  caseZ :  (e : Exp 0 M) → (e' : Exp 1 M) → case (val Z) of e # e' ↦R e
  caseS : {ef : Exp 0 M} → (e : Exp 0 M) → (e' : Exp 1 M)   
                → case (val (S ef)) of e # e' ↦R e' [- ef -]

