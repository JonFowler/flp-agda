module Subs where

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
  
data Holes : Sub → Set where
  hole : Holes hole
  inS : {s : Sub} → (h : Holes s) → Holes (S s)
  

  
outS : ∀{h} → Holes (S h) → Holes h
outS (inS h) = h
  
Binding : Sub → Set
Binding s = Holes s → Sub 

Bindings : ∀{n} → Subs n → Set
Bindings = VecI Binding

id-Bind : (s : Sub) → Binding s
id-Bind s p = hole

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
  
≤ₛ-look : ∀{s s'} (p : Holes s) → s ≤ₛ s' → Sub
≤ₛ-look hole (≤hole s) = s
≤ₛ-look (inS p) (≤inS s) = ≤ₛ-look p s

updateP : {s : Sub} → (p : Holes s) → (s' : Sub)  → Sub
updateP  hole s' = s'
updateP  (inS p) s' = S (updateP p s')


≤ₛ-look' : ∀{s s'} (p : Holes s) → s ≤ₛ s' → 
         Σ Sub (λ s'' → updateP p s'' ≤ₛ s')
≤ₛ-look' hole (≤hole s') = s' , ≤ₛ-refl 
≤ₛ-look' (inS p) (≤inS b) with ≤ₛ-look' p b
...| (s' , b') = s' , ≤inS b'

≤ₛ-point : ∀{s} → (p : Holes s) → (s' : Sub) → s ≤ₛ updateP p s' 
≤ₛ-point hole s' = ≤hole s'
≤ₛ-point (inS p) s' = ≤inS (≤ₛ-point p s') 

updatePhole : ∀{s} (p : Holes s) → updateP {s} p hole ≡ s 
updatePhole hole = refl
updatePhole (inS p) = cong S (updatePhole p)

--partUpdate : {s s'' : Sub} → (p : Holes s) → (s' : Sub) → 
--              (le : s ≤ₛ s'') → s' ≤ₛ lookupP p le → updateP p s' ≤ₛ s''
--partUpdate hole s' (≤hole s'') le' = le'
--partUpdate (inS p) s' (≤inS le) le' = ≤inS (partUpdate p s' le le')


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

_:b_ : ∀{s}(b : Binding s) → Binding (updateSub s b) → Binding s
_:b_ {Z} b b' ()
_:b_ {S s} b b' = (b ∘ inS) :b (b' ∘ inS) ∘ outS
_:b_ {hole} b b' hole = updateSub (b hole) b'

compb : ∀{s}(b : Binding s)(b' : Binding (updateSub s b)) → updateSub (updateSub s b) b' ≡ updateSub s (b :b b')
compb {Z} b b' = refl 
compb {S s} b b' = cong S (compb (b ∘ inS) (b' ∘ inS)) 
compb {hole} b b' = refl

_⇨ₛ_ : Sub → Sub → Set
s ⇨ₛ s' = Σ (Binding s) (λ b → s' ≡ updateSub s b)

_⇨_ : ∀{m} → Subs m → Subs m → Set
_⇨_ = VecI₂ _⇨ₛ_ --Σ (Bindings M) (λ B → M' ≡ (zipWithI updateSub M B) )


⇨ₛ-refl : ∀{s} → s ⇨ₛ s
⇨ₛ-refl {Z} = (λ ()) , refl
⇨ₛ-refl {S x} with ⇨ₛ-refl {x}
...| (b , eq) = b ∘ outS , cong S eq
⇨ₛ-refl {hole} = (λ x → hole) , refl

⇨-refl : ∀{m}{M : Subs m} → M ⇨ M
⇨-refl {M = []} = []
⇨-refl {M = x ∷ M} = ⇨ₛ-refl  ∷ ⇨-refl

_∘⇨ₛ_ : ∀{s s' s''} →  s' ⇨ₛ s'' → s ⇨ₛ s' → s ⇨ₛ s'' 
(b' , refl) ∘⇨ₛ (b , refl) = b :b b' , compb b b'

_∘⇨_ : ∀{m}{M M' M'' : Subs m} →  M' ⇨ M'' → M ⇨ M' → M ⇨ M'' 
[] ∘⇨ [] = []
(b' ∷ B') ∘⇨ (b ∷ B) = (b' ∘⇨ₛ b) ∷ B' ∘⇨ B

⇨ₛ-uniq : ∀{s s'} → (b : s ⇨ₛ s') → (b' : s ⇨ₛ s') → b ≡ b'
⇨ₛ-uniq {s} (b , refl) (b' , eq') with b-uniq {s} eq' 
⇨ₛ-uniq (b , refl) (.b , eq) | refl with eq 
⇨ₛ-uniq (b , refl) (.b , eq) | refl | refl = refl 

⇨-uniq : ∀{m}{M M' : Subs m} (B : M ⇨ M') → (B' : M ⇨ M') → B ≡ B'
⇨-uniq [] [] = refl
⇨-uniq (x ∷ B) (x₁ ∷ B') = cong₂ _∷_ (⇨ₛ-uniq x x₁) (⇨-uniq B B')

EmptyPos : ∀{s s'} → Holes s → (s ⇨ₛ s') → Set
EmptyPos p (b , eq) = b p ≡ hole

--splitp : ∀{s s'} (p : Holes s) → s ⇨ₛ s' → 
--         Σ Sub (λ s'' → Σ (updateP p s'' ⇨ₛ s') (EmptyPos (addPos p ()))
--splitp = {!!}

bindPoint : ∀{s} → (p : Holes s) → (s' : Sub) → s ⇨ₛ updateP p s' 
bindPoint hole s' = (λ x → s') , refl
bindPoint (inS p) s' with bindPoint p s'
bindPoint (inS p) s' | b , eq = (b ∘ outS) , cong S eq

⇨-point : ∀{m s'}{M : Subs m} → (x : Fin m) → (lookup x M ⇨ₛ s') → 
                  M ⇨ insert x s' M
⇨-point {M = s ∷ M} zero b = b ∷ ⇨-refl
⇨-point {M = s ∷ M} (suc x) b = ⇨ₛ-refl ∷ ⇨-point x b

bindingZ : ∀{m}{M : Subs m} (x : Fin m) → (p : Holes (lookup x M)) → M ⇨ insert x (updateP p Z) M
bindingZ x p = ⇨-point x (bindPoint p Z)

bindingS :  ∀{m}{M : Subs m} (x : Fin m) → (p : Holes (lookup x M)) → M ⇨ insert x (updateP p (S hole)) M
bindingS x p = ⇨-point x (bindPoint p (S hole))



--bindS : ∀{s} → (p : Holes s) → s ⇨ₛ updateP p (S hole) 
--bindS p = bindpoint p (S hole)





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


data ValPos (s : Sub) : Set where
  S : ValPos s → ValPos s
  Z : ValPos s
  pos : Holes s → ValPos s
  
upd-assoc : ∀{s s' s''} → (p : Holes s) → (p' : Holes s') →  updateP {updateP {s} p s'} (joinPos p p') s'' ≡ updateP {s} p (updateP {s'} p' s'') 
upd-assoc hole p' = refl
upd-assoc (inS p) p' = cong S (upd-assoc p p')

mapValPos : ∀{s s'} → ((Holes s) → (ValPos s')) → ValPos s → ValPos s'
mapValPos f (S t) = S (mapValPos f t)
mapValPos f Z = Z
mapValPos f (pos x) = f x 

valPosP : (s : Sub) → ValPos s 
valPosP Z = Z
valPosP (S s) = mapValPos (pos ∘ inS) (valPosP s) 
valPosP hole = pos hole 

liftPoint : ∀{s}(p : Holes s) → (b : Binding s) → Holes (b p) → Holes (updateSub s b)
liftPoint hole b p' = p' 
liftPoint (inS p) b p' = inS (liftPoint p (b ∘ inS) p')

liftPoint' : ∀{s s'}(p : Holes s) → (b : s ≤ₛ s') → Holes (≤ₛ-look p b) → Holes s' 
liftPoint' hole (≤hole s) p' = p'
liftPoint' (inS p) (≤inS r) p' = inS (liftPoint' p r p')

--liftPoint'' : ∀{s s' s''}(p : Holes s) → (updateP p s'' ≡ s') → Holes s'' → Holes s' 
--liftPoint'' hole (≤hole s) p' = p'
--liftPoint'' (inS p) (≤inS r) p' = inS (liftPoint' p r p')



--valPos : ∀{s s'} → (p : Holes s) → (b : s ⇨ₛ s') → ValPos s' 
--valPos p (b , eq) = let r = valPosP p (b p) in 
--        mapValPos (subst (λ x → Holes (updateP p (b p)) → x) (cong ValPos (sym eq)) 
--                         (pos ∘ (liftPoint p b))) r
--(subst (λ p' → Holes (updateP p (b p)) → Holes p') ? (liftPoint p b)) r  

valPos' : ∀{s s'} → (p : Holes s) → (b : s ≤ₛ s') → ValPos s' 
valPos' p b = let s = ≤ₛ-look p b in
    mapValPos (pos ∘ liftPoint' p b) (valPosP s)


--valPos-refl : ∀{s} → (p : Holes s) → (b : s ≤ₛ s) → pos p ≡ valPos' p b
--valPos-refl p b with ≤ₛ-look p b
--...| c  = {!!}
--valPos-refl hole (≤hole .hole) = refl
--valPos-refl (inS p) (≤inS b) = let r = (valPos-refl p b) in {!!}

valPos-join : ∀{s s' s''} → (p : Holes s) → (b : s ≤ₛ s') → (b' : s' ≤ₛ s'') → 
           valPos' p (b' ≤ₛ∘ b) ≡ mapValPos (λ p' → valPos' p' b') (valPos' p b)
valPos-join p b b' = {!!}

