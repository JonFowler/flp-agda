module Sub where

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import VecI
open import Function
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
  
data Pos : Sub → Set where
  here : Pos hole
  there : ∀{s} → (Pos s) → Pos (S s)
  
--data _∈ₛ_ : Pos → Sub → Set where
--  here : here ∈ₛ hole 
--  there : ∀{p s} → p ∈ₛ s → there p ∈ₛ S s 
  
--_+ₚ_ : Pos → Pos → Pos
--here +ₚ p = p
--there p +ₚ p' = there (p +ₚ p')



Inp : Sub → Set
Inp hole = ⊥
Inp Z = Unit
Inp (S s) = Inp s


data _≤ₛ_ : Sub → Sub → Set where
  ≤ₛ-hole : (s : Sub) → hole ≤ₛ s 
  ≤ₛ-Z : Z ≤ₛ Z 
  ≤ₛ-S : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'

_≤_ : {m : ℕ} → Subs m → Subs m → Set
_≤_ = VecI₂ _≤ₛ_ 

≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤ₛ-hole hole
≤ₛ-refl {Z} = ≤ₛ-Z 
≤ₛ-refl {S s} = ≤ₛ-S ≤ₛ-refl 


≤ₛ-trans : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
≤ₛ-trans {s'' = s''} (≤ₛ-hole s) o' = ≤ₛ-hole s''
≤ₛ-trans ≤ₛ-Z ≤ₛ-Z = ≤ₛ-Z
≤ₛ-trans (≤ₛ-S o) (≤ₛ-S o') = ≤ₛ-S (≤ₛ-trans o o')

_≤ₛ-∘_ : ∀{s s' s''} → s' ≤ₛ s'' → s ≤ₛ s' → s ≤ₛ s''
_≤ₛ-∘_ {s'' = s''} o' (≤ₛ-hole s) = ≤ₛ-hole s''
_≤ₛ-∘_ ≤ₛ-Z ≤ₛ-Z = ≤ₛ-Z
_≤ₛ-∘_ (≤ₛ-S o') (≤ₛ-S o) = ≤ₛ-S (o' ≤ₛ-∘ o)

≤ₛ-uniq : ∀{s s'} → (o : s ≤ₛ s') → (o' : s ≤ₛ s') → o ≡ o' 
≤ₛ-uniq (≤ₛ-hole s) (≤ₛ-hole .s) = refl
≤ₛ-uniq ≤ₛ-Z ≤ₛ-Z = refl
≤ₛ-uniq (≤ₛ-S o) (≤ₛ-S o') = cong ≤ₛ-S (≤ₛ-uniq o o') 


≤-refl : ∀{m} {σ : Subs m} → σ ≤ σ
≤-refl {σ = []} = []
≤-refl {σ = x ∷ σ} = ≤ₛ-refl {x} ∷ ≤-refl

≤-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤ σ' → σ' ≤ σ'' → σ ≤ σ''
≤-trans [] [] = []
≤-trans {suc m}{s ∷ _}{s' ∷ _} (o ∷ os) (o' ∷ os') = ≤ₛ-trans {s}{s'} o o' ∷ ≤-trans os os' 

_≤-∘_ : ∀{m} {σ σ' σ'' : Subs m} → σ' ≤ σ'' → σ ≤ σ' → σ ≤ σ''
_≤-∘_ [] [] = []
_≤-∘_ {suc m}{s ∷ _}{s' ∷ _} (o' ∷ os') (o ∷ os) = _≤ₛ-∘_ {s}{s'} o' o ∷ (os' ≤-∘ os)



--updateS : Sub → Pos → Sub → Sub
--updateS s here s' = s 
--updateS s (there p) (S n) = S (updateS s p n)
--updateS s (there p) a  = hole
--
--lookupS : Pos → Sub → Sub
--lookupS here s = s
--lookupS (there p) (S s) = lookupS p s
--lookupS (there p) s = hole


--∈-lookupS : ∀{p s} → p ∈ₛ s → hole ≡ lookupS p s → p ∈ₛ s
--∈-lookupS {here} {hole} x = unit
--∈-lookupS {here} {Z} ()
--∈-lookupS {here} {S s} ()
--∈-lookupS {there p} {hole} x = {!x!}
--∈-lookupS {there p} {Z} x = {!!}
--∈-lookupS {there p} {S s} x = {!!}

--outS : Sub → Sub
--outS hole = hole
--outS Z = Z
--outS (S s) = s
--
--there-lookupS : ∀{s s'}(p : Pos) → S s' ≡ lookupS p s → s' ≡ lookupS (there p) s
--there-lookupS {hole} (here)  ()
--there-lookupS {Z}   (here) () 
--there-lookupS {S s} (here)  eq = cong outS eq
--there-lookupS {hole} (there p)  ()
--there-lookupS {Z} (there p) ()
--there-lookupS {S s} (there p) eq = there-lookupS p eq 
--
--lookupS-mono : ∀{s s'} → (p : Pos) → s ≤ₛ s' → lookupS p s ≤ₛ lookupS p s'
--lookupS-mono here o = o
--lookupS-mono (there p) (≤ₛ-hole s) = ≤ₛ-hole (lookupS (there p) s)
--lookupS-mono (there p) ≤ₛ-Z = ≤ₛ-hole hole
--lookupS-mono (there p) (≤ₛ-S o) = lookupS-mono p o





data ValPos (s : Sub) : Set where
  pos : (p : Pos s) → ValPos s
  Z : ValPos s
  S : ValPos s → ValPos s
  
--data ValPosI (P : Pos → Set) : ValPos → Set where
--  S : ∀{vp} → ValPosI P vp → ValPosI P (S vp)
--  Z : ValPosI P Z
--  pos : ∀{p} → P p → ValPosI P (pos p )
--
--_∈ₚ_ : ValPos → Sub → Set
--vp ∈ₚ s = ValPosI (λ p' → p' ∈ₛ s) vp
--  
_=<<_ : ∀{s s'} → (Pos s → ValPos s') → ValPos s → ValPos s'
_=<<_ f (pos x) = f x
_=<<_ f Z = Z
_=<<_ f (S vp) = S (f =<< vp)

return : ∀{s} → Pos s → ValPos s
return = pos

left-ret : ∀{s} → (vp : ValPos s) → return =<< vp ≡ vp
left-ret (pos x) = refl
left-ret Z = refl
left-ret (S vp) = cong S (left-ret vp)

right-ret : ∀{s s'} (f : Pos s → ValPos s') → (p : Pos s) → f =<< return p ≡ f p
right-ret f p = refl

=<<-assoc : ∀{s s' s''} (f : Pos s → ValPos s') → (g : Pos s' → ValPos s'') → (vp : ValPos s) → g =<< (f =<< vp) ≡ (λ p → g =<< f p) =<< vp
=<<-assoc f g (pos x) = refl
=<<-assoc f g Z = refl
=<<-assoc f g (S vp) = cong S (=<<-assoc f g vp)

posThere : ∀{s} → Pos s → ValPos (S s)
posThere p = pos (there p)

conv : (s : Sub)  → ValPos s
conv hole = pos here
conv Z = Z
conv (S s) = S (posThere =<< conv s)

toValPos : ∀{s s'} → Pos s → s ≤ₛ s' → ValPos s'
toValPos here (≤ₛ-hole s) = conv s
toValPos (there p) (≤ₛ-S o) = posThere =<< toValPos p o

toValPos-refl : ∀{s} → (p : Pos s) → (o : s ≤ₛ s) → toValPos p o ≡ pos p 
toValPos-refl here (≤ₛ-hole .hole) = refl
toValPos-refl (there p) (≤ₛ-S o) = cong (_=<<_ posThere) (toValPos-refl p o)

toValPos-ord : ∀{s s' s''} → (p : Pos s) → (o : s ≤ₛ s') → (o' : s' ≤ₛ s'') 
          → (λ p' → toValPos p' o') =<< (toValPos p o) ≡ toValPos p (o' ≤ₛ-∘ o)
toValPos-ord here (≤ₛ-hole hole) (≤ₛ-hole s) = refl
toValPos-ord here (≤ₛ-hole Z) ≤ₛ-Z = refl
toValPos-ord here (≤ₛ-hole (S s)) (≤ₛ-S o') = 
  cong S (trans (=<<-assoc posThere (λ p' → toValPos p' (≤ₛ-S o')) (conv s)) 
         (trans (sym (=<<-assoc (λ p' → toValPos p' o') posThere (conv s))) 
         (cong (_=<<_ posThere) (toValPos-ord here (≤ₛ-hole s) o'))))
toValPos-ord (there p) (≤ₛ-S o) (≤ₛ-S o') = 
  trans (=<<-assoc posThere (λ p' → toValPos p' (≤ₛ-S o')) (toValPos p o)) 
  (trans (sym (=<<-assoc (λ p' → toValPos p' o') posThere (toValPos p o))) 
  (cong (_=<<_ posThere) (toValPos-ord p o o')))
