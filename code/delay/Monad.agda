{-# OPTIONS --without-K #-}

module delay.Monad where

open import Data.Product
open import Function 

open import delay.Delay

-- Monadic bind

mutual
  bindD : ∀ {i A B} → (A → Delay' i B) → Delay' i A → Delay' i B
  bindD f (now x) = f x
  bindD f (later x) = later (∞bindD f x)

  ∞bindD : ∀ {i A B} → (A → Delay' i B) → ∞Delay' i A → ∞Delay' i B
  force (∞bindD f x) = bindD f (force x)

-- Bind and convergence

bindD↓ : ∀ {A B} (f : A → Delay B) (x : Delay A) {b : B}
  → bindD f x ↓ b → Σ A (λ a → x ↓ a × f a ↓ b)
bindD↓ f (now x) p = x , now , p
bindD↓ f (later x) (laterL p) = let (a , q , r) = bindD↓ f (force x) p in a , laterL q , r

bindD-input↓ : ∀ {A B} (f : A → Delay B) {x : Delay A} {a : A}
  → x ↓ a → bindD f x ≈ f a
bindD-input↓ f now = refl≈
bindD-input↓ f (laterL p) = laterL (bindD-input↓ f p)  

mutual
  cong-bindD : ∀ {A B} {f : A → Delay B} {x y : Delay A}
    → x ≈ y → bindD f x ≈ bindD f y
  cong-bindD now = refl≈
  cong-bindD (later p) = later (∞cong-bindD (force p))
  cong-bindD (laterL p) = laterL (cong-bindD p)
  cong-bindD (laterR p) = laterR (cong-bindD p)

  ∞cong-bindD : ∀ {A B} {f : A → Delay B} {x y : Delay A}
    → x ≈ y → bindD f x ∞≈ bindD f y
  force (∞cong-bindD p) = cong-bindD p

-- Action on morphisms

mapD : ∀ {i A B} → (A → B) → Delay' i A → Delay' i B
mapD f = bindD (now ∘ f)

-- Composition in the Kleisli category

infix  40 _∙_

_∙_ : {A B C : Set} → (B → Delay C) → (A → Delay B) → A → Delay C
g ∙ f = bindD g ∘ f

-- Equality of morphisms in the Kleisli category

infixl  3 _∼_

_∼_ : {A B : Set} (f g : A → Delay B) → Set
f ∼ g = ∀ x → f x ≈ g x

refl∼ : {A B : Set} {f : A → Delay B} → f ∼ f
refl∼ x = refl≈

sym∼ : {A B : Set} {f g : A → Delay B} → f ∼ g → g ∼ f
sym∼ p x = sym≈ (p x)

trans∼ : {A B : Set} {f g h : A → Delay B}
  → f ∼ g → g ∼ h → f ∼ h
trans∼ p q x = trans≈ (p x) (q x)  

mutual
  cong-app-bindD : ∀ {A B} {f f' : A → Delay B} (x : Delay A)
    → f ∼ f' → bindD f x ≈ bindD f' x
  cong-app-bindD (now x) p = p x
  cong-app-bindD (later x) p = later (∞cong-app-bindD (force x) p)
  
  ∞cong-app-bindD : ∀ {A B} {f f' : A → Delay B} (x : Delay A)
    → f ∼ f' → bindD f x ∞≈ bindD f' x
  force (∞cong-app-bindD x p) = cong-app-bindD x p

cong-bindD₂ : ∀ {A B} {f f' : A → Delay B} {x x' : Delay A}
    → f ∼ f' → x ≈ x' → bindD f x ≈ bindD f' x'
cong-bindD₂ {x' = x'} p q = trans≈ (cong-bindD q) (cong-app-bindD x' p)    


mutual
  M2 : ∀ {A} (x : Delay A) → bindD now x ≈ x
  M2 (now x) = now
  M2 (later x) = later (∞M2 (force x))

  ∞M2 : ∀ {A} (x : Delay A) → bindD now x ∞≈ x
  force (∞M2 x) = M2 x

mutual
  M3 : ∀ {A B C} {g : B → Delay C} {f : A → Delay B} (x : Delay A)
    → bindD g (bindD f x) ≈ bindD (bindD g ∘ f) x
  M3 (now x) = refl≈
  M3 (later x) = later (∞M3 (force x))  

  ∞M3 : ∀ {A B C} {g : B → Delay C} {f : A → Delay B} (x : Delay A)
    → bindD g (bindD f x) ∞≈ bindD (bindD g ∘ f) x
  force (∞M3 x) = M3 x

bind-mapD : ∀ {A B C} {f : A → B} {g : B → Delay C}
  → g ∙ mapD f ∼ bindD (g ∘ f)
bind-mapD = M3

-- Strength

str : ∀ {i A B} → A × Delay' i B → Delay' i (A × B)
str (x , y) = mapD < (λ _ → x) , id > y

costr : ∀ {i A B} → Delay' i B × A → Delay' i (B × A)
costr (x , y) = mapD < id , (λ _ → y) > x

cong∙ : ∀ {A B C} {g g' : B → Delay C} {f f' : A → Delay B}
    → g ∼ g' → f ∼ f' → g ∙ f ∼ g' ∙ f'
cong∙ {f = f} p q x = trans≈ (cong-app-bindD (f x) p) (cong-bindD (q x))

{-
_∙∼_ : ∀ {A B C} (g : B → Delay C) {f f' : A → Delay B}
    → f ∼ f' → g ∙ f ∼ g ∙ f'
(g ∙∼ p) x = cong-bindD (p x)     

_∼∙_ : ∀ {A B C} {g g' : B → Delay C} → g ∼ g'
  → (f : A → Delay B) → g ∙ f ∼ g' ∙ f
(p ∼∙ f) x = cong-bindD2 (f x) p
-}

assoc∙ : {A B C D : Set} {f : A → Delay B} {g : B → Delay C} {h : C → Delay D}
  → h ∙ (g ∙ f) ∼ (h ∙ g) ∙ f
assoc∙ {f = f} x = M3 (f x)




-- Equational reasoning sugar for ≈
module Eq≈ where
  infix 4 _≋_
  infix 1 proof_
  infixr 2 _≈〈_〉_
  infix 3 _qed
  
  data _≋_ {A : Set} (x y : Delay A) : Set where
    relto : x ≈ y → x ≋ y
  
  proof_ : {A : Set} {x y : Delay A} → x ≋ y → x ≈ y
  proof relto p = p
  
  _≈〈_〉_ :  {A : Set} (x : Delay A) {y z : Delay A} → x ≈ y → y ≋ z → x ≋ z
  _ ≈〈 p 〉 relto q = relto (trans≈ p q)
  
  _qed  :  {A : Set} (x : Delay A) → x ≋ x
  _qed _ = relto refl≈


-- Equational reasoning sugar for ∼
module Eq∼ where
  infix 4 _∼'_
  infix 1 proof_
  infixr 2 _∼〈_〉_
  infix 3 _qed
  
  data _∼'_ {A B : Set} (x y : A → Delay B) : Set where
    relto : x ∼ y → x ∼' y
    
  proof_ : {A B : Set} {x y : A → Delay B} → x ∼' y → x ∼ y
  proof relto p = p
  
  _∼〈_〉_ :  {A B : Set} (x : A → Delay B) {y z : A → Delay B} → x ∼ y → y ∼' z → x ∼' z
  _ ∼〈 p 〉 relto q = relto (trans∼ p q)
  
  _qed  :  {A B : Set} (x : A → Delay B) → x ∼' x
  _qed _ = relto refl∼


