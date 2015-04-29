module VecI where

open import Data.Vec
open import Data.Nat hiding (_⊔_)
open import Data.Fin
open import Function
open import Data.Product
open import Agda.Primitive
open import Relation.Binary.PropositionalEquality

data VecI {γ γ'} {A : Set γ} (P : A → Set γ') :  {n : ℕ} → Vec A n → Set (γ ⊔ γ') where
   [] : VecI P []
   _∷_ : ∀{n}{a : A}{As : Vec A n} → P a → VecI P As → VecI P (a ∷ As)
   
data VecI₂ {γ γ'} {A B : Set γ} (P : A → B → Set γ') :  
           {n : ℕ} → Vec A n → Vec B n → Set (γ ⊔ γ') where
   [] : VecI₂ P [] []
   _∷_ : ∀{n}{a : A}{b : B}{as : Vec A n}{bs : Vec B n} → P a b → VecI₂ P as bs → VecI₂ P (a ∷ as) (b ∷ bs)
   
update : ∀{n}{A : Set} → Fin n → (A → A) →  Vec A n → Vec A n
update zero f (a ∷ as) = f a ∷ as
update (suc i) f (a ∷ as) = a ∷ update i f as

insert : ∀{n}{A : Set} → (x : Fin n) → A →  Vec A n → Vec A n
insert i a as = update i (const a) as

upd-look : ∀{n}{A : Set} → (x : Fin n) → (f : A → A) → (σ : Vec A n) → f (lookup x σ) ≡ lookup x (update x f σ)
upd-look zero f (s ∷ σ) = refl
upd-look (suc x) f (s ∷ σ) = upd-look x f σ 

ins-look : ∀{n}{A : Set}(x : Fin n) → (a : A) → (σ : Vec A n) → a ≡ lookup x (insert x a σ)
ins-look x a σ = upd-look x (const a) σ 

lookupI : ∀{n}{A : Set}{P : A → Set}{As : Vec A n} → (i : Fin n) → VecI P As → P (lookup i As)
lookupI zero (x ∷ as) = x
lookupI (suc i) (x ∷ as) = lookupI i as

repeatI : ∀{n}{A : Set}{P : A → Set}(As : Vec A n) → (f : (a : A) → P a) → VecI P As 
repeatI [] f = []
repeatI (x ∷ as) f = f x ∷ repeatI as f


lookupI₂ : ∀{n}{A B : Set}{P : A → B → Set}{As : Vec A n}{Bs : Vec B n} 
         → (i : Fin n) → VecI₂ P As Bs → P (lookup i As) (lookup i Bs)
lookupI₂ zero (x ∷ as) = x
lookupI₂ (suc i) (x ∷ as) = lookupI₂ i as

updateI : ∀{n}{A : Set}{P : A → Set}{As : Vec A n}{a' : A} → (i : Fin n) → 
          (f : P (lookup i As) → P a') → VecI P As → VecI P (insert i a' As)
updateI zero f (x ∷ as) = f x ∷ as
updateI (suc i) f (x ∷ as) = x ∷ updateI i f as

updateI₂ : ∀{n}{A B : Set}{P : A → B → Set}{As : Vec A n}{Bs : Vec B n}{a : A}{b : B} → (i : Fin n) → 
          (f : P (lookup i As) (lookup i Bs) → P a b) → VecI₂ P As Bs → VecI₂ P (insert i a As) (insert i b Bs)
updateI₂ zero f (x ∷ as) = f x ∷ as
updateI₂ (suc i) f (x ∷ as) = x ∷ updateI₂ i f as



zipI : ∀{n}{A : Set}{P : A → Set} → (as : Vec A n) → VecI P as → Vec (Σ A P) n
zipI [] [] = []
zipI (a ∷ as) (p ∷ ps) = (a , p) ∷ zipI as ps

zipWithI : ∀{n}{A B : Set}{P : A → Set}(f : (a : A) → P a → B) → (as : Vec A n) → VecI P as 
         → Vec B n
zipWithI f [] [] = []
zipWithI f (a ∷ as) (p ∷ ps) = f a p ∷ zipWithI f as ps

zipWithI-lookup : ∀{n}{A B : Set}{P : A → Set}(x : Fin n) → (f : (a : A) → P a → B) → (as : Vec A n) → (bs : VecI P as) → lookup x (zipWithI f as bs) ≡ f (lookup x as) (lookupI x bs)
zipWithI-lookup zero f (a ∷ as) (b ∷ bs) = refl
zipWithI-lookup (suc x) f (a ∷ as) (b ∷ bs) = zipWithI-lookup x f as bs

--insertI : ∀{n γ}{A : Set γ}{As : Vec (Set γ) n} → (i : Fin n) → 
--          A → VecI As → VecI (insert i A As)
--insertI i a = updateI i (const a) 
--
----upd-lookI : ∀{n γ}{A : Set γ}{As : Vec (Set γ) n} → 
----          (i : Fin n) → (f : lookup i As → A) → (as : VecI As) → 
----            f (lookupI i as) ≡ lookupI i (updateI i f as)
----upd-lookI zero f (s ∷ σ) = refl
----upd-lookI (suc x) f (s ∷ σ) = upd-look x f σ 
--
----ins-look x a σ = upd-look x (const a) σ 
--
--Vec1 : ∀{γ}{A : Set}(P : A → Set γ) → Set (lsuc γ)
--Vec1 P = {!As : Vec (P!}
 
