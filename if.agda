module if where

open import Data.Sum
open import Data.Container
open import Data.Maybe
open import Data.Product
open import Relation.Binary.PropositionalEquality

data Val : Set where
  true : Val
  false : Val

--data Exp : Set where
--   val : Val → Exp
--   if_then_else_ : (a b c : Exp) → Exp 
--
--data Hole : Set where
--  hole : Hole
--  ifsubj : Hole → (b c : Exp) → Hole
--  
--data Ctx : 

record _⊆_ (A : Set) (B : Set) : Set₁ where
  field 
    sub : B → Set
    emb : A → B 
    out : Σ B sub → A
    embin : (a : A) → sub (emb a)
    outemb : {a : A} → out (emb a , embin a) ≡ a
    embout : {b : Σ B sub} → emb (out b) ≡ proj₁ b

data Exp (A : Set) : Set where
  if_then_else_ : (a b c : A ) → Exp A
  val : Val → Exp A 
  
data Red {A : Set}{P : Val ⊆ A} : Exp A → A → Set where
   iftrue : {b c : A} → Red (if (_⊆_.emb P true) then b else c) b
--   iffalse : (b c : A ⊎ Val) → Red (if (inj₂ false) then b else c) c
   
--data Ctx {A : Set} (P : A → A ⊎ Val → Set) : Exp A → Exp A ⊎ Val → Set where
--   subj : {a : A}{a' b c : A ⊎ Val} → P a a' → 
--                Ctx P (if inj₁ a then b else c) (inj₁ (if a' then b else c) )
 
--data Fix (f : Set → Set) : Set where
--  In : f (Fix f) → Fix f

data Fix : Set where
  In : Exp Fix → Fix 
  
--_↦_ : Exp Fix → Exp Fix → Set
--_↦_ = Ctx (λ e a → Red {!!} a) 
