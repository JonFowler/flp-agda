module Subs2 where

open import VecI
open import Helpful
open import Data.Vec
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Data.Fin hiding (_≤_)
open import Function
open import Data.Unit hiding (_≤_)

postulate ext : {A B : Set} {f₁ : A → B} {f₂ : A → B} → 
                                      ((x : A) → f₁ x ≡ f₂ x) → f₁ ≡ f₂
                                      
rext :  {A B : Set} {f₁ : A → B} {f₂ : A → B} → 
                                       f₁ ≡ f₂ → ((x : A) → f₁ x ≡ f₂ x) 
rext refl x = refl

data Sub : Set where
  Z : Sub
  S : Sub → Sub
  hole : Sub
  
Subs : ℕ → Set
Subs = Vec Sub
  
data Pos : Set where
  hole : Pos 
  inS : (p : Pos) → Pos
  
data _∈ₛ_ : Pos → Sub → Set where
  hole : hole ∈ₛ hole
  inS : ∀{p s} → p ∈ₛ s → inS p ∈ₛ S s

data _≤ₛ_ : Sub → Sub → Set where
  ≤hole : (s : Sub) → hole ≤ₛ s
  ≤Z : Z ≤ₛ Z 
  ≤inS : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'
  
≤ₛ-look : ∀{s s'} (p : Pos) → s ≤ₛ s' → Sub
≤ₛ-look hole (≤hole s) = s
≤ₛ-look hole ≤Z = Z
≤ₛ-look hole (≤inS b) = S (≤ₛ-look hole b) 
≤ₛ-look (inS p) (≤hole Z) = hole
≤ₛ-look (inS p) (≤hole (S s)) = ≤ₛ-look p (≤hole s)
≤ₛ-look (inS p) (≤hole hole) = hole
≤ₛ-look (inS p) ≤Z = hole
≤ₛ-look (inS p) (≤inS b) = ≤ₛ-look p b

--∈-look : ∀{p s s'} (p ∈ₛ s) → s ≤ₛ s' → Sub
--∈-look = {!!}

updateP : (s' : Sub) → (p : Pos) →  (s : Sub)  → Sub
updateP s' hole s = s'
updateP s' (inS p) (S s) = updateP s' p s
updateP s' (inS p) a = hole

--≤ₛ-point : ∀{s} → (p : Pos) → (s' : Sub) → s ≤ₛ updateP p s' s 
--≤ₛ-point {Z} hole s' = {!!}
--≤ₛ-point {S s} hole s' = {!!}
--≤ₛ-point {hole} hole s' = ≤hole s'
--≤ₛ-point (inS p) s' = {!!}

--updatePhole : ∀{s} (p : Holes s) → updateP {s} p hole ≡ s 
--updatePhole hole = refl
--updatePhole (inS p) = cong S (updatePhole p)
--
----partUpdate : {s s'' : Sub} → (p : Holes s) → (s' : Sub) → 
----              (le : s ≤ₛ s'') → s' ≤ₛ lookupP p le → updateP p s' ≤ₛ s''
----partUpdate hole s' (≤hole s'') le' = le'
----partUpdate (inS p) s' (≤inS le) le' = ≤inS (partUpdate p s' le le')
--
--updateH : ∀{s} → (p : Holes s) → Holes (updateP p (S hole)) 
--updateH hole = inS hole
--updateH (inS p) = inS (updateH p)
--
--joinPos : ∀{s s'} → (p : Holes s) → (p' : Holes s') → 
--     Holes (updateP p s') 
--joinPos hole p' = p'
--joinPos (inS p) p' = inS (joinPos p p')
--
--updateSub : ∀{s s'} → p →     → updateP p (S hole) s ≤ s'
--updateSub : (s : Sub) → Binding s → Sub
--updateSub Z f = Z
--updateSub (S x) f = S (updateSub x (f ∘ inS))
--updateSub hole f = f hole

--embedHole : ∀{s} → (b : Binding s) → (p : Holes s) → hole ≡ b p → Holes (updateSub s b)
--embedHole b hole e = subst Holes e hole
--embedHole b (inS p) e = inS (embedHole (b ∘ inS) p e)
--
--b-uniq : ∀{s}{b b' : Binding s} → updateSub s b ≡ updateSub s b' → b ≡ b'
--b-uniq {Z} eq = ext (λ ())
--b-uniq {S s}{b}{b'} eq = let r = b-uniq {s} (outValS eq) in ext (λ {(inS h) → cong-app r h}) 
--b-uniq {hole}{b}{b'} eq = ext x
--  where x : (h : Holes hole) → b h ≡ b' h
--        x hole = eq
--
--bindingZ : ∀{m}{M : Subs m} (x : Fin m) → (p : Holes (lookup x M)) → M ⇨ insert x (updateP p Z) M
--bindingZ x p = ⇨-point x (bindPoint p Z)
--
--bindingS :  ∀{m}{M : Subs m} (x : Fin m) → (p : Holes (lookup x M)) → M ⇨ insert x (updateP p (S hole)) M
--bindingS x p = ⇨-point x (bindPoint p (S hole))
--
--
_≤_ : ∀{M} → Subs M → Subs M → Set
_≤_ = VecI₂ _≤ₛ_

-- Ordering is reflexive
≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤hole hole
≤ₛ-refl {Z} = ≤Z
≤ₛ-refl {S s} = ≤inS ≤ₛ-refl
                                        
-- Transitivity (composability) of ordering
_≤ₛ∘_ : ∀{s s' s''} → s' ≤ₛ s'' → s ≤ₛ s' → s ≤ₛ s''
_≤ₛ∘_ {s'' = s''} o' (≤hole s) = ≤hole s'' 
_≤ₛ∘_ o' ≤Z = o'
_≤ₛ∘_ (≤inS o') (≤inS o) = ≤inS (o' ≤ₛ∘ o)

-- Lifting reflectivity to environment order
≤s-refl : ∀{m} {σ : Subs m} → σ ≤ σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤ₛ-refl ∷ ≤s-refl

-- Lifting transivity to environment order
_≤s∘_ : ∀{m} {σ σ' σ'' : Subs m} → σ' ≤ σ'' → σ ≤ σ' → σ ≤ σ''
_≤s∘_ [] [] = []
_≤s∘_ (s' ∷ o') (s ∷ o) = s' ≤ₛ∘ s ∷ o' ≤s∘ o 

--data Bind : Sub → Sub → Set where
--  bindZ : Bind hole Z
--  bindS : Bind hole (S hole) 
--  inS : ∀{s s'} → Bind s s' → Bind (S s) (S s')

_<ₛ_ : Sub → Sub → Set
s <ₛ s' = s ≤ₛ s' × s ≠ s'
----
----Minimal : {A : Set} → (ord : A → A → Set) → (P : A → Set) → (x : A) →  Set
----Minimal {A} ord P x = (y : A) → (P y) → ord y x → x ≡ y
----  
----Bind : Sub → Set
----Bind s = Σ Sub (Minimal _≤ₛ_ (_<ₛ_ s))
--
--
data ValPos : Set where
  S : ValPos → ValPos
  Z : ValPos
  pos : Pos → ValPos
  
data _∈ₚ_ : ValPos → Sub → Set where
  S : ∀{s vp} → vp ∈ₚ s → S vp ∈ₚ s
  Z : ∀{s} → Z ∈ₚ s
  pos : ∀{s p} → p ∈ₛ s → pos p ∈ₚ s
  
--upd-assoc : ∀{s s' s''} → (p : Holes s) → (p' : Holes s') →  updateP {updateP {s} p s'} (joinPos p p') s'' ≡ updateP {s} p (updateP {s'} p' s'') 
--upd-assoc hole p' = refl
--upd-assoc (inS p) p' = cong S (upd-assoc p p')
--
valPosP : (p : Pos) →  (s : Sub) → ValPos 
valPosP p Z = Z
valPosP p (S s) = valPosP (inS p) s
valPosP p hole = pos p

--liftPoint : ∀{s}(p : Holes s) → (b : Binding s) → Holes (updateP p (b p)) → Holes (updateSub s b)
--liftPoint hole b p' with b hole
--liftPoint hole b p' | c = p'
--liftPoint (inS p) b (inS p') = inS (liftPoint p (b ∘ inS) p')
--
--liftPoint' : ∀{s s'}(p : Holes s) → (b : s ≤ₛ s') → Holes (updateP p (≤ₛ-look p b)) → Holes s' 
--liftPoint' hole (≤hole s) h = h
--liftPoint' (inS p) (≤inS r) (inS h) = inS (liftPoint' p r h)

mapValPos : (Pos → ValPos) → ValPos → ValPos 
mapValPos f (S t) = S (mapValPos f t)
mapValPos f Z = Z
mapValPos f (pos x) = f x 

valPos : ∀{s s'} → (p : Pos) → (b : s ≤ₛ s') → ValPos 
valPos hole (≤hole s) = valPosP hole s
valPos hole ≤Z = valPosP hole Z
valPos hole (≤inS b) = {!valPosP hole !}
valPos (inS p) b = {!!} 

∈-valPos : ∀{p s s'} → (p ∈ₛ s) → (b : s ≤ₛ s') → valPos p b ∈ₚ s'
∈-valPos hole (≤hole Z) = Z 
∈-valPos {hole} hole (≤hole (S s)) = {!S!}
∈-valPos hole (≤hole hole) = pos hole
∈-valPos (inS i) (≤inS b) = {!!}
      
----valPos-refl : ∀{s} → (p : Holes s) → (b : s ≤ₛ s) → pos p ≡ valPos' p b
----valPos-refl p b with ≤ₛ-look p b
----...| c  = {!!}
----valPos-refl hole (≤hole .hole) = refl
----valPos-refl (inS p) (≤inS b) = let r = (valPos-refl p b) in {!!}
--
valPos-join : ∀{s s' s''} → (p : Pos) → (b : s ≤ₛ s') → (b' : s' ≤ₛ s'') → 
           valPos p (b' ≤ₛ∘ b) ≡ mapValPos (λ p' → valPos p' b') (valPos p b)
valPos-join hole (≤hole s) b' = {!!}
valPos-join hole ≤Z b' = {!!}
valPos-join hole (≤inS b) b' = {!!}
valPos-join (inS p) b b' = {!!}

