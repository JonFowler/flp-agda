module Subs where

open import VecI
open import Helpful
open import Data.Vec
open import Data.Nat hiding (_≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Empty
open import Function
open import Data.Unit

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
  
data Holes : Sub → Set where
  hole : Holes hole
  inS : {s : Sub} → (h : Holes s) → Holes (S s)
  
outS : ∀{h} → Holes (S h) → Holes h
outS (inS h) = h
  
Binding : Sub → Set
Binding s = Holes s → Sub 

Bindings : ∀{n} → Subs n → Set
Bindings = VecI Binding

outValS : {b c : Sub} → S b ≡ S c → b ≡ c
outValS refl = refl

--decSub : (a b : Sub) → Dec (a ≡ b)
--decSub (val Z) (val Z) = yes refl
--decSub (val Z) (val (S x)) = no (λ ())
--decSub (val (S x)) (val Z) = no (λ ())
--decSub (val (S x)) (val (S x₁)) with decSub x x₁ 
--decSub (val (S x)) (val (S x₁)) | yes p = yes (cong (val ∘ S) p)
--decSub (val (S x)) (val (S x₁)) | no ¬p = no (λ p → ¬p (outValS p))
--decSub (val x) (hole unit) = no (λ ())
--decSub hole (val x) = no (λ ())
--decSub hole hole = yes refl


--bindingDec' : ∀ {s} → (b1 b2 : Binding s) → Dec ((x : Holes s) → b1 x ≡ b2 x)
--bindingDec' {val Z} b1 b2 = yes (λ ())
--bindingDec' {val (S x)} b1 b2 with bindingDec' (b1 ∘ inS) (b2 ∘ inS) 
--bindingDec' {val (S x)} b1 b2 | yes p = yes (λ {(inS x') → p x'})
--bindingDec' {val (S x)} b1 b2 | no ¬p = no (λ z → ¬p (z ∘ inS))
--bindingDec' {hole} b1 b2 with decSub (b1 hole) (b2 hole)
--bindingDec' {hole} b1 b2 | yes p = yes (λ {hole → p})
--bindingDec' {hole} b1 b2 | no ¬p = no (λ z → ¬p (z hole))

--bindingDec : ∀ {s} → (b1 b2 : Binding s) → Dec (b1 ≡ b2)
--bindingDec b1 b2 with bindingDec' b1 b2 
--bindingDec b1 b2 | yes p = yes (ext p)
--bindingDec b1 b2 | no ¬p = no (λ x → ¬p (rext x))
  
data _≤ₛ_ : Sub → Sub → Set where
  ≤hole : (s : Sub) → hole ≤ₛ s
  ≤Z : Z ≤ₛ Z 
  ≤inS : ∀{s s'} → s ≤ₛ s' → S s ≤ₛ S s'
  
lookupP : ∀{s s'} (p : Holes s) → s ≤ₛ s' → Sub
lookupP hole (≤hole s) = s
lookupP (inS p) (≤inS s) = lookupP p s

updateP : {s : Sub} → (p : Holes s) → (s' : Sub)  → Sub
updateP  hole s' = s'
updateP  (inS p) s' = S (updateP p s')

updatePhole : ∀{s} (p : Holes s) → updateP {s} p hole ≡ s 
updatePhole hole = refl
updatePhole (inS p) = cong S (updatePhole p)

partUpdate : {s s'' : Sub} → (p : Holes s) → (s' : Sub) → 
              (le : s ≤ₛ s'') → s' ≤ₛ lookupP p le → updateP p s' ≤ₛ s''
partUpdate hole s' (≤hole s'') le' = le'
partUpdate (inS p) s' (≤inS le) le' = ≤inS (partUpdate p s' le le')

updateH : ∀{s} → (p : Holes s) → Holes (updateP p (S hole)) 
updateH hole = inS hole
updateH (inS p) = inS (updateH p)

joinPos : ∀{s s'} → (p : Holes s) → (p' : Holes s') → 
     Holes (updateP p s') 
joinPos hole p' = p'
joinPos (inS p) p' = inS (joinPos p p')

--: ∀{s s'} → p →     → updateP p (S hole) s ≤ s'
updateSub : (s : Sub) → Binding s → Sub
updateSub Z f = Z
updateSub (S x) f = S (updateSub x (f ∘ inS))
updateSub hole f = f hole

embedHole : ∀{s} → (b : Binding s) → (p : Holes s) → hole ≡ b p → Holes (updateSub s b)
embedHole b hole e = subst Holes e hole
embedHole b (inS p) e = inS (embedHole (b ∘ inS) p e)

b-uniq : ∀{s}{b b' : Binding s} → updateSub s b ≡ updateSub s b' → b ≡ b'
b-uniq {Z} eq = ext (λ ())
b-uniq {S s}{b}{b'} eq = let r = b-uniq {s} (outValS eq) in ext (λ {(inS h) → cong-app r h}) 
b-uniq {hole}{b}{b'} eq = ext x
  where x : (h : Holes hole) → b h ≡ b' h
        x hole = eq

_∶b_ : ∀{s}(b : Binding s) → Binding (updateSub s b) → Binding s
_∶b_ {Z} b b' ()
_∶b_ {S s} b b' = (b ∘ inS) ∶b (b' ∘ inS) ∘ outS
_∶b_ {hole} b b' hole = updateSub (b hole) b'

compb : ∀{s}(b : Binding s)(b' : Binding (updateSub s b)) → updateSub (updateSub s b) b' ≡ updateSub s (b ∶b b')
compb {Z} b b' = refl 
compb {S s} b b' = cong S (compb (b ∘ inS) (b' ∘ inS)) 
compb {hole} b b' = refl

_⇨_ : Sub → Sub → Set
s ⇨ s' = Σ (Binding s) (λ b → s' ≡ updateSub s b)

_⇨M_ : ∀{m} → Subs m → Subs m → Set
M ⇨M M' = Σ (Bindings M) (λ B → M' ≡ (zipWithI updateSub M B) )

⇨-refl : ∀{s} → s ⇨ s
⇨-refl {Z} = (λ ()) , refl
⇨-refl {S x} with ⇨-refl {x}
...| (b , eq) = b ∘ outS , cong S eq
⇨-refl {hole} = (λ x → hole) , refl

_∶⇨_ : ∀{s s' s''} → s ⇨ s' → s' ⇨ s'' → s ⇨ s'' 
(b , refl) ∶⇨ (b' , refl) = b ∶b b' , compb b b'

⇨-uniq : ∀{s s'} → (b : s ⇨ s') → (b' : s ⇨ s') → b ≡ b'
⇨-uniq {s} (b , refl) (b' , eq') with b-uniq {s} eq' 
⇨-uniq (b , refl) (.b , eq) | refl with eq 
⇨-uniq (b , refl) (.b , eq) | refl | refl = refl 

--toVal : {s : Sub} → Holes s → (b : Binding s) → Sub (Holes (updateSub s b))
--toVal hole b with b hole 
--toVal hole b | val Z = val Z
--toVal hole b | val (S x) = val (S ({!!}))
--toVal hole b | hole unit = hole hole
--toVal (inS h) b = {!!} 

--⇨-equiv : ∀{s s'} → s ⇨ s' → s ≤ₛ s'
--⇨-equiv {val Z} (proj₁ , refl) = ≤Z
--⇨-equiv {val (S x)} (b , refl) = ≤inS (⇨-equiv (b ∘ inS , refl))
--⇨-equiv {hole} (proj₁ , proj₂) = ≤hole
--
--
--≤ₛ-equiv : ∀{s s'} → s ≤ₛ s' → s ⇨ s' 
--≤ₛ-equiv {hole}{s'} ≤hole = (λ x → s') , refl
--≤ₛ-equiv ≤Z = (λ ()) , refl
--≤ₛ-equiv (≤inS le) with ≤ₛ-equiv le 
--≤ₛ-equiv (≤inS le) | b , refl = b ∘ outS , refl 
--  
--SubVars : ∀{M} → Subs M → Set
--SubVars = VecI Holes 
--
_≤s_ : ∀{M} → Subs M → Subs M → Set
_≤s_ = VecI₂ _≤ₛ_

-- Ordering is reflexive
≤ₛ-refl : ∀{s} → s ≤ₛ s
≤ₛ-refl {hole} = ≤hole hole
≤ₛ-refl {Z} = ≤Z
≤ₛ-refl {S s} = ≤inS ≤ₛ-refl
                                        
-- Transitivity (composability) of ordering
_≤ₛ∘_ : ∀{s s' s''} → s ≤ₛ s' → s' ≤ₛ s'' → s ≤ₛ s''
_≤ₛ∘_ {s'' = s''} (≤hole s) o' = ≤hole s'' 
_≤ₛ∘_ ≤Z o' = o'
_≤ₛ∘_ (≤inS o) (≤inS o') = ≤inS (o ≤ₛ∘ o')

-- Lifting reflectivity to environment order
≤s-refl : ∀{m} {σ : Subs m} → σ ≤s σ
≤s-refl {σ = []} = []
≤s-refl {σ = x ∷ σ} = ≤ₛ-refl ∷ ≤s-refl

-- Lifting transivity to environment order
_≤s∘_ : ∀{m} {σ σ' σ'' : Subs m} → σ ≤s σ' → σ' ≤s σ'' → σ ≤s σ''
_≤s∘_ [] [] = []
_≤s∘_ (s ∷ o) (s' ∷ o') = s ≤ₛ∘ s' ∷ o ≤s∘ o' 

--data Bind : Sub → Sub → Set where
--  bindZ : Bind hole Z
--  bindS : Bind hole (S hole) 
--  inS : ∀{s s'} → Bind s s' → Bind (S s) (S s')

_<ₛ_ : Sub → Sub → Set
s <ₛ s' = s ≤ₛ s' × s ≠ s'
--
--Minimal : {A : Set} → (ord : A → A → Set) → (P : A → Set) → (x : A) →  Set
--Minimal {A} ord P x = (y : A) → (P y) → ord y x → x ≡ y
--  
--Bind : Sub → Set
--Bind s = Σ Sub (Minimal _≤ₛ_ (_<ₛ_ s))


data Test (s : Sub) : Set where
  S : Test s → Test s
  Z : Test s
  pos : Holes s → Test s
  
--convert p b with b p | inspect b p 
--convert p b | Z    | [ eq ] = Z
--convert {s} p b | S c  | [ eq ] = 
--  let r = convert (inS p) (b ∘ outS) 
--  in S  (subst Test {!!} r) 
--convert p b | hole | [ eq ] = pos (embedHole b p (sym eq))

upd-assoc : ∀{s s' s''} → (p : Holes s) → (p' : Holes s') →  updateP {updateP {s} p s'} (joinPos p p') s'' ≡ updateP {s} p (updateP {s'} p' s'') 
upd-assoc hole p' = refl
upd-assoc (inS p) p' = cong S (upd-assoc p p')

convert' : ∀{s} → (p : Holes s) → (s' : Sub) → Test (updateP p s')
convert' p Z = Z
convert' p (S s') = let r = convert' (joinPos p (inS hole)) s' 
     in S (subst Test (upd-assoc p (inS hole)) r)
convert' p hole = pos (subst Holes (sym (updatePhole p)) p) 

bindPoint : ∀{s}(p : Holes s) → (b : Binding s) → Holes (updateP p (b p)) → Holes (updateSub s b)
bindPoint hole b p' with b hole
bindPoint hole b () | Z
bindPoint hole b  p' | S c = p'
bindPoint hole b p' | hole = p'
bindPoint (inS p) b (inS p') = inS (bindPoint p (b ∘ inS) p')

mapTest : ∀{s s'} → ((Holes s) → (Holes s')) → Test s → Test s'
mapTest f (S t) = S (mapTest f t)
mapTest f Z = Z
mapTest f (pos x) = pos (f x) 

convert : ∀{s} → (p : Holes s) → (b : Binding s) → Test (updateSub s b)
convert p b = let r = convert' p (b p) in 
        mapTest (bindPoint p b) r
