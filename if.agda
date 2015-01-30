module if where

open import Data.Sum
open import Data.Container

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

data Exp (A : Set) : Set where
  if_then_else_ : (a b c : A ⊎ Val) → Exp A
  
data Red {A : Set} : Exp A → A ⊎ Val → Set where
   iftrue : (b c : A ⊎ Val) → Red (if (inj₂ true) then b else c) b
   iffalse : (b c : A ⊎ Val) → Red (if (inj₂ false) then b else c) c
   
data Ctx {A : Set} (P : A → A ⊎ Val → Set) : Exp A → Exp A → Set where
   subj : {a : A}{a' b c : A ⊎ Val} → P a a' → 
                Ctx P (if inj₁ a then b else c) (if a' then b else c) 
 
--data Fix (f : Set → Set) : Set where
--  In : f (Fix f) → Fix f

data Fix : Set where
  In : Exp Fix → Fix 

