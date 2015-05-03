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
  
_+ₚ_ : Pos → Pos → Pos
hole +ₚ p' = p'
inS p +ₚ p' = inS (p +ₚ p')

+ₚ-id : ∀{p} → p +ₚ hole ≡ p
+ₚ-id {hole} = refl
+ₚ-id {inS p} = cong inS +ₚ-id 

+ₚ-assoc : (p p' p'' : Pos) → (p +ₚ p') +ₚ p'' ≡ p +ₚ (p' +ₚ p'')
+ₚ-assoc hole p' p'' = refl
+ₚ-assoc (inS p) p' p'' = cong inS (+ₚ-assoc p p' p'')
  
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

≤ₛ-look-refl : ∀{p s} → (p ∈ₛ s) → (b : s ≤ₛ s) → ≤ₛ-look p b ≡ hole
≤ₛ-look-refl hole (≤hole .hole) = refl
≤ₛ-look-refl (inS p) (≤inS b) = ≤ₛ-look-refl p b


updateP : (s' : Sub) → (p : Pos) →  (s : Sub)  → Sub
updateP s' hole s = s'
updateP s' (inS p) (S s) = updateP s' p s
updateP s' (inS p) a = hole

--updateP-                updateP s'' (p +ₚ p') (updateP s' p s) ≡ updateP (updateP s'' p' s') p s 

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
  
data ValPosI (P : Pos → Set) : ValPos → Set where
  S : ∀{vp} → ValPosI P vp → ValPosI P (S vp)
  Z : ValPosI P Z
  pos : ∀{p} → P p → ValPosI P (pos p )

_∈ₚ_ : ValPos → Sub → Set
vp ∈ₚ s = ValPosI (λ p' → p' ∈ₛ s) vp
 
  
mapValPos : (Pos → ValPos) → ValPos → ValPos 
mapValPos f (S t) = S (mapValPos f t)
mapValPos f Z = Z
mapValPos f (pos x) = f x 

comp-mapValPos : (f g : Pos → ValPos) → (vp : ValPos) → mapValPos g (mapValPos f vp) ≡ mapValPos (mapValPos g ∘ f) vp
comp-mapValPos f g (S vp) = cong S (comp-mapValPos f g vp)
comp-mapValPos f g Z = refl
comp-mapValPos f g (pos x) = refl

gen-mapValPos : ∀{vp P Q}{f : Pos → ValPos} →  ({p : Pos} → P p → ValPosI Q (f p)) → ValPosI P vp → ValPosI Q (mapValPos f vp) 
gen-mapValPos f' (S vp) = S (gen-mapValPos f' vp)
gen-mapValPos f' Z = Z
gen-mapValPos f' (pos x) = f' x


--gen-mapValPos : ∀{s' vp}{s : Sub}{f : Pos → ValPos} →  ({p : Pos} → p ∈ₛ s → f p ∈ₚ s') → vp ∈ₚ s → mapValPos f vp ∈ₚ s'

  
--upd-assoc : ∀{s s' s''} → (p : Holes s) → (p' : Holes s') →  updateP {updateP {s} p s'} (joinPos p p') s'' ≡ updateP {s} p (updateP {s'} p' s'') 
--upd-assoc hole p' = refl
--upd-assoc (inS p) p' = cong S (upd-assoc p p')
--
valPosP : (s : Sub) → ValPos 
valPosP Z = Z
valPosP (S s) = S (mapValPos (λ x → pos (inS x)) (valPosP s))
valPosP hole = pos hole

∈-valPosP  : (s : Sub) →  valPosP s ∈ₚ s 
∈-valPosP Z = Z
∈-valPosP (S s) = S (gen-mapValPos (λ x → pos (inS x)) (∈-valPosP s))
∈-valPosP hole = pos hole

--liftPoint : ∀{s}(p : Holes s) → (b : Binding s) → Holes (updateP p (b p)) → Holes (updateSub s b)
--liftPoint hole b p' with b hole
--liftPoint hole b p' | c = p'
--liftPoint (inS p) b (inS p') = inS (liftPoint p (b ∘ inS) p')
--
--liftPoint' : ∀{s s'}(p : Holes s) → (b : s ≤ₛ s') → Holes (updateP p (≤ₛ-look p b)) → Holes s' 
--liftPoint' hole (≤hole s) h = h
--liftPoint' (inS p) (≤inS r) (inS h) = inS (liftPoint' p r h)

valPos : ∀{s s'} → (p : Pos) → (b : s ≤ₛ s') → ValPos 
valPos p b = mapValPos (λ p' → pos (p +ₚ p')) (valPosP (≤ₛ-look p b))

∈-+ₚ : ∀{p p' s s'} → (b : s ≤ₛ s') → (p ∈ₛ s) → (p' ∈ₛ ≤ₛ-look p b) → (p +ₚ p') ∈ₛ s'
∈-+ₚ (≤hole s) hole p' = p'
∈-+ₚ (≤inS b) (inS p) p' = inS (∈-+ₚ b p p') -- {! (∈-+ₚ b p p')!}

∈-valPos : ∀{p s s'} → (p ∈ₛ s) → (b : s ≤ₛ s') → valPos p b ∈ₚ s'
∈-valPos {p}{s}{s'} i b = gen-mapValPos (λ x → pos (∈-+ₚ b i x)) (∈-valPosP (≤ₛ-look p b)) 

valPos-refl : ∀{p s} → (p ∈ₛ s) → (b : s ≤ₛ s) → valPos p b ≡ pos p 
valPos-refl {p = p} i b = 
            let r = ≤ₛ-look-refl i b 
                y = cong valPosP r 
                z = cong (mapValPos (λ p' → pos (p +ₚ p'))) y  in trans z (cong pos +ₚ-id)
                
--test : mapValPos (λ p' → pos (p +ₚ p'))  (valPosP (≤ₛ-look p (b' ≤ₛ∘ b))) 


valPos-join : ∀{s s' s''} → (p : Pos) → (b : s ≤ₛ s') → (b' : s' ≤ₛ s'') → 
           valPos p (b' ≤ₛ∘ b) ≡ mapValPos (λ p' → valPos p' b') (valPos p b)
valPos-join hole b b' = {!b!}
valPos-join (inS p) b b' = {!!} 
--  let r = sym (comp-mapValPos (λ z → pos (p +ₚ z)) (λ p' → valPos p' b') (valPosP (≤ₛ-look p b) )) 
--  in trans {!!} r 
--valPos-join hole ≤Z b' = {!!}
--valPos-join hole (≤inS b) b' = {!!}
--valPos-join (inS p) b b' = {!!}

