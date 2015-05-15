module Sub where

open import Data.Unit hiding (_≤_)
open import Data.Empty
open import Data.Product
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_)
open import VecI
open import Function
open import Data.Vec
open import Relation.Binary.PropositionalEquality

postulate ext : ∀ {A B : Set} {f g : A → B} → ({x : A} → f x ≡ g x) → f ≡ g


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

--Bind : Sub → Set
--Bind s = (p : Pos s) → Sub

data Bind : Sub → Set where
  b-hole : (s : Sub) → Bind hole
  b-Z : Bind Z
  b-S : ∀{s} → (b : Bind s) → Bind (S s) 

b-refl : ∀{s} → Bind s
b-refl {hole} = b-hole hole
b-refl {Z} = b-Z
b-refl {S s} = b-S b-refl

_⟦ₛ_⟧ : (s : Sub) → Bind s → Sub
hole ⟦ₛ b-hole s ⟧ = s 
Z ⟦ₛ b-Z ⟧ = Z 
S s ⟦ₛ b-S b ⟧ = S (s ⟦ₛ b ⟧)

_∶-_ : ∀{s} (b : Bind s) → (b' : Bind (s ⟦ₛ b ⟧)) → Bind s
b-hole s ∶- b' = b-hole (s ⟦ₛ b' ⟧)
b-Z ∶- b-Z = b-Z
b-S b ∶- b-S b' = b-S (b ∶- b')

⟦ₛ⟧-func : (s : Sub) → (b : Bind s) → (b' : Bind (s ⟦ₛ b ⟧)) → s ⟦ₛ b ⟧ ⟦ₛ b' ⟧ ≡ s ⟦ₛ b ∶- b' ⟧
⟦ₛ⟧-func hole (b-hole s) b' = refl 
⟦ₛ⟧-func Z b-Z b-Z = refl  
⟦ₛ⟧-func (S s) (b-S b) (b-S b') = cong S (⟦ₛ⟧-func s b b') 

⟦ₛ⟧-refl : ∀{s} → s ⟦ₛ b-refl ⟧ ≡ s
⟦ₛ⟧-refl {hole} = refl
⟦ₛ⟧-refl {Z} = refl
⟦ₛ⟧-refl {S s} = cong S ⟦ₛ⟧-refl 


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

≤-uniq : ∀{m}{σ σ' : Subs m} → (o : σ ≤ σ') → (o' : σ ≤ σ') → o ≡ o' 
≤-uniq [] [] = refl
≤-uniq (x ∷ o) (x₁ ∷ o') = cong₂ (_∷_) (≤ₛ-uniq x x₁) (≤-uniq o o')

_[ₛ_] : {s s' : Sub} → (b : s ≤ₛ s') → Pos s → Sub
≤ₛ-hole s [ₛ here ] = s
≤ₛ-S b [ₛ there p ] = b [ₛ p ]

[ₛ]-refl : ∀{s} → (b : s ≤ₛ s) → (p : Pos s) →  b [ₛ p ] ≡ hole
[ₛ]-refl (≤ₛ-hole .hole) here = refl
[ₛ]-refl (≤ₛ-S b) (there p) = [ₛ]-refl b p

_[_//ₛ_] : (s : Sub) →  (Pos s) → Sub → Sub
_[_//ₛ_] hole here s' = s'
_[_//ₛ_] (S s) (there p) s' = S  (s [ p //ₛ s' ])

_+⟨_,_⟩_ : ∀{s s' s''} → (p : Pos s) → (b : s ≤ₛ s') → (b [ₛ p ] ≡ s'') → (p' : Pos s'') → Pos s'
here +⟨ ≤ₛ-hole s , refl ⟩ p' = p' -- p'
there p +⟨ ≤ₛ-S b , eq ⟩ p' = there (p +⟨ b , eq ⟩ p') -- there (p +ₚ p')



addp : ∀{s s'} → (p : Pos s) → (b : s ≤ₛ s') → (p' : Pos (b [ₛ p ])) → Pos s'
addp here (≤ₛ-hole s) p' = p'
addp (there p) (≤ₛ-S b) p' = there (addp p b p')

addp2 : ∀{s s' s''} → (p : Pos s) → (b : s ≤ₛ s') → (b [ₛ p ] ≡ s'') → (p' : Pos s'') → Pos s'
addp2 p b refl p' = addp p b p'

addp-refl : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → (p' : Pos (b [ₛ p ])) → addp p b p' ≡ p
addp-refl here (≤ₛ-hole .hole) here = refl
addp-refl (there p) (≤ₛ-S b) p' = cong there (addp-refl p b p')


+⟨⟩-refl : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → (p' : Pos hole) → p +⟨ b , [ₛ]-refl b p ⟩ p' ≡ p
+⟨⟩-refl here (≤ₛ-hole .hole) here = refl
+⟨⟩-refl (there p) (≤ₛ-S b) p' = cong there (+⟨⟩-refl p b p')

minimal : Sub → Set
minimal Z = Unit
minimal (S hole) = Unit
minimal _ = ⊥ 

_/ₛ_ :   {s : Sub} → (p : Pos s) → (s' : Sub)  → s ≤ₛ s [ p //ₛ s' ]
here /ₛ s' = ≤ₛ-hole s'
(there p) /ₛ s' = ≤ₛ-S (p /ₛ s')



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

--toValPos : ∀{s} → (p : Pos s) → (b : Bind s) → ValPos (s ⟦ₛ b ⟧)
--toValPos here (b-hole s) = conv s
--toValPos (there p) (b-S b) = posThere =<< toValPos p b

toValPos : ∀{s s'} → Pos s → s ≤ₛ s' → ValPos s'
toValPos p b = (λ p' → pos (p +⟨ b , refl ⟩ p')) =<< conv (b [ₛ p ])

--toValPos here (≤ₛ-hole s) = conv s
--toValPos (there p) (≤ₛ-S o) = _+ₚ_ p =<< toValPos p o


Test : ∀{s} (p : Pos s) → (b : s ≤ₛ s) → Set
Test p b = Σ Sub (λ s → b [ₛ p ] ≡ s)

J : {A : Set}{a b : A}(C : (a : A) → (b : A) → (a ≡ b) → Set) → (o : a ≡ b) → C a a refl → C a b o
J C refl c = c

test'' : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → Test p b 
test'' p b = (b [ₛ p ]) , refl

test''' : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → Test p b 
test''' p b = hole , ([ₛ]-refl b p)

twotests :  ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → test'' p b ≡ test''' p b
twotests here (≤ₛ-hole .hole) = refl 
twotests (there p) (≤ₛ-S b) = twotests p b

--J (λ x y eq →  (x , {!!}) ≡ (y , {!!})) ([ₛ]-refl b p) {!!}


twotests' :  ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → test'' p b ≡ test''' p b
twotests' p b = {!!}

test : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → ( (λ p' → pos (addp2 p b refl p')) =<< conv (b [ₛ p ])  ) ≡ pos p 
test p b = let
     q = J (λ x y eq →  ( (λ p' → pos (addp2 p b (proj₂ y) p')) =<< conv (proj₁ y)) ≡ pos p) (sym (twotests p b))  {!!} 
  in {!!}
  
cong' : {A B : Set}{x y : A} (P : A → B) → (x ≡ y) → P x ≡ P y
cong' P eq = J (λ a b x → P a ≡ P b) eq refl 

eqlift : {A : Set} {a b : A} → (q : a ≡ b) → (a , refl {x = a}) ≡ (b , q)
eqlift {A}{a}{b} q = J (λ a' b' x' → (a' , refl) ≡ (b' , x')) q refl -- (refl {x = (a , refl)})

subst' : {A : Set}{x y : A} (P : A → Set) → (x ≡ y) → P x → P y
subst' P eq p = J (λ a b x → P b) eq p

substEq : {A : Set}{x y : A} (P : (a : A) → (x ≡ a) → Set) → (eq : x ≡ y) → P x refl → P y eq
substEq P eq p = J (λ {(a , eqa) (b , eqb) x → P b eqb}) (eqlift eq) p

J' : {A : Set}{a b : A}(C : (a : A) → (b : A) → (a ≡ b) → Set) → (o : a ≡ b) → C a a refl → C a b o
J' {a = a}{b = b} C e c = substEq (λ b' eq → C a b' eq) e c

toValPos-refl : ∀{s} → (p : Pos s) → (b : s ≤ₛ s) → toValPos p b ≡ pos p 
toValPos-refl p b = let
                coerce₁ = subst 
            in subst₂ {!!} {!!} {!!} {!!} 

--here (≤ₛ-hole .hole) = refl
--toValPos-refl (there p) (≤ₛ-S o) = cong (_=<<_ posThere) (toValPos-refl p o)

--toValPos-func : ∀{s s' s''} → (p : Pos s) → (o : s ≤ₛ s') → (o' : s' ≤ₛ s'') 
--          → (λ p' → toValPos p' o') =<< (toValPos p o) ≡ toValPos p (o' ≤ₛ-∘ o)
--toValPos-func here (≤ₛ-hole hole) (≤ₛ-hole s) = refl
--toValPos-func here (≤ₛ-hole Z) ≤ₛ-Z = refl
--toValPos-func here (≤ₛ-hole (S s)) (≤ₛ-S o') = 
--  cong S (trans (=<<-assoc posThere (λ p' → toValPos p' (≤ₛ-S o')) (conv s)) 
--         (trans (sym (=<<-assoc (λ p' → toValPos p' o') posThere (conv s))) 
--         (cong (_=<<_ posThere) (toValPos-func here (≤ₛ-hole s) o'))))
--toValPos-func (there p) (≤ₛ-S o) (≤ₛ-S o') = 
--  trans (=<<-assoc posThere (λ p' → toValPos p' (≤ₛ-S o')) (toValPos p o)) 
--  (trans (sym (=<<-assoc (λ p' → toValPos p' o') posThere (toValPos p o))) 
--  (cong (_=<<_ posThere) (toValPos-func p o o')))
