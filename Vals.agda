module Vals where


record Cont (A : Set) : Set where
     

data ICont (I : (A : Set) → Cont A) : Set where
