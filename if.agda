module if where

data Val : Set where
  true : Val
  false : Val

data Exp (A : Set) : Set where
   val : Val → Exp A
   if_then_else_ : (a b c : A) → Exp A

data Red {A : Set} (P : A → Val B) : Exp A → Val B → Set where
  redIfTrue : 
