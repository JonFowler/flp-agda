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

≤-refl : ∀{m} {σ : Subs m} → σ ≤ σ
≤-refl {σ = []} = []
≤-refl {σ = x ∷ σ} = ≤ₛ-refl {x} ∷ ≤-refl

≤-trans : ∀{m} {σ σ' σ'' : Subs m} → σ ≤ σ' → σ' ≤ σ'' → σ ≤ σ''
≤-trans [] [] = []
≤-trans {suc m}{s ∷ _}{s' ∷ _} (o ∷ os) (o' ∷ os') = ≤ₛ-trans {s}{s'} o o' ∷ ≤-trans os os' 



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





--data ValPos : Set where
--  pos : Pos → ValPos
--  Z : ValPos
--  S : ValPos → ValPos
--  
--data ValPosI (P : Pos → Set) : ValPos → Set where
--  S : ∀{vp} → ValPosI P vp → ValPosI P (S vp)
--  Z : ValPosI P Z
--  pos : ∀{p} → P p → ValPosI P (pos p )
--
--_∈ₚ_ : ValPos → Sub → Set
--vp ∈ₚ s = ValPosI (λ p' → p' ∈ₛ s) vp
--  
--_=<<_ : (Pos → ValPos) → ValPos → ValPos
--_=<<_ f (pos x) = f x
--_=<<_ f Z = Z
--_=<<_ f (S vp) = S (f =<< vp)
--
--return : Pos → ValPos
--return = pos
--
--left-ret : (vp : ValPos) → return =<< vp ≡ vp
--left-ret (pos x) = refl
--left-ret Z = refl
--left-ret (S vp) = cong S (left-ret vp)
--
--right-ret : (f : Pos → ValPos) → (p : Pos) → f =<< return p ≡ f p
--right-ret f p = refl
--
--=<<-assoc : (f g : Pos → ValPos) → (vp : ValPos) → f =<< (g =<< vp) ≡ (λ p → f =<< g p) =<< vp
--=<<-assoc f g (pos x) = refl
--=<<-assoc f g Z = refl
--=<<-assoc f g (S vp) = cong S (=<<-assoc f g vp)
--
--_=<<I_ : ∀{vp P Q}{f : Pos → ValPos} →  ({p : Pos} → P p → ValPosI Q (f p)) → ValPosI P vp → ValPosI Q (f =<< vp)
--_=<<I_ f (S p) = S (f =<<I p)
--_=<<I_ f Z = Z
--_=<<I_ f (pos x) = f x
--
--posThere : Pos → ValPos
--posThere p = pos (there p)
--
--conv : Sub → ValPos
--conv hole = pos here
--conv Z = Z
--conv (S s) = S (posThere =<< conv s)
--
--∈-conv : (s : Sub) → conv s ∈ₚ s
--∈-conv hole = pos here
--∈-conv Z = Z
--∈-conv (S s) = S ((λ p → pos (there p)) =<<I (∈-conv s))
--
--toValPos : ∀{s s' p} → p ∈ₛ s → s ≤ₛ s' → ValPos
--toValPos here (≤ₛ-hole s) = conv s
--toValPos (there p) (≤ₛ-S o) = posThere =<< toValPos p o
--
--∈-toValPos : ∀{s s' p} → (i : p ∈ₛ s) → (o : s ≤ₛ s') → toValPos i o ∈ₚ s'
--∈-toValPos here (≤ₛ-hole s) = ∈-conv s
--∈-toValPos (there i) (≤ₛ-S o) = (λ p → pos (there p)) =<<I ∈-toValPos i o

--toValPos-ord : ∀{s s' s'' p} → (i : p ∈ₛ s) → (o : s ≤ₛ s') → (o' : s' ≤ₛ s'') 
--          → (λ p → toValPos (∈-toValPos i o)) >>= (toValPos i o)
--toValPos-ord = ?
