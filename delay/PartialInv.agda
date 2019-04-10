{-# OPTIONS --without-K #-}

module delay.PartialInv where

open import Data.Product
open import Function 
open import Relation.Binary.PropositionalEquality

open import delay.Delay
open import delay.Monad

-- Partial equivalences

record is-partial-inv {A B : Set} (f : A → Delay B) : Set where
  constructor pinv
  field
    g : B → Delay A
    α : ∀ a b → g b ↓ a → f a ↓ b
    β : ∀ b a → f a ↓ b → g b ↓ a

_≃₁_ : Set → Set → Set
A ≃₁ B = Σ (A → Delay B) is-partial-inv

sem-dagger : ∀{A B} → A ≃₁ B → B ≃₁ A
sem-dagger (f , pinv g α β) = g , (pinv f β α)

_≃₂_ : ∀ {A B} → A ≃₁ B → A ≃₁ B → Set
(f , _) ≃₂ (g , _) = f ∼ g

-- Categorically, partial equivalences are defined in terms of Cockett
-- and Lack's restriction operation.  The Kleisli category of Delay is
-- indeed a restriction category.  We do not formally prove all the
-- restriction laws, but we show that is-partial-inv is equivalent to
-- the notion of partial equivalence based on restriction.

-- Restriction operation
-- PS: This is how to define restriction for equational lifting monads.

⌊_⌋ : {A B : Set} → (A → Delay B) → A → Delay A
⌊ f ⌋ = mapD proj₁ ∘ str ∘ < id , f > 

cong-rest : {A B : Set} {f g : A → Delay B} → f ∼ g → ⌊ f ⌋ ∼ ⌊ g ⌋
cong-rest p x = cong-bindD (cong-bindD (p x))

record is-partial-inv-rest {A B : Set} (f : A → Delay B) : Set where
  constructor pinv-rest
  field
    g : B → Delay A
    α : f ∙ g ∼ ⌊ g ⌋
    β : g ∙ f ∼ ⌊ f ⌋

linv-equiv₁ : {A B : Set}
  → (f : A → Delay B) (g : B → Delay A) → g ∙ f ∼ ⌊ f ⌋
  → ∀ b a → f a ↓ b → g b ↓ a
linv-equiv₁ f g p b a q = trans≈ (cong-bindD (sym≈ q)) (trans≈ (p _) (cong-bindD (cong-bindD q)))

linv-equiv₂' : {A B : Set}
  → (f : A → Delay B) (g : B → Delay A) 
  → (∀ b a → f a ↓ b → g b ↓ a)
  → (x {y} : A) → bindD g (f x) ↓ y → ⌊ f ⌋ x ↓ y
linv-equiv₂' f g p a q with bindD↓ g (f a) q
... | (b , r , s) with unique↓ s (p _ _ r)
linv-equiv₂' f g p a q | b , r , s | refl = 
  bindD-input↓ (λ x → now (proj₁ x)) (bindD-input↓ (λ x → now (a , x)) r)

linv-equiv₂'' : {A B : Set}
  → (f : A → Delay B) (g : B → Delay A) 
  → (∀ b a → f a ↓ b → g b ↓ a)
  → (x {y} : A) → ⌊ f ⌋ x ↓ y → bindD g (f x) ↓ y
linv-equiv₂'' f g p a q with bindD↓ (λ x → now (proj₁ x)) (bindD (λ x → now (a , x)) (f a)) q
linv-equiv₂'' f g p a q | (a' , b) , r , s with bindD↓ (λ x → now (a , x)) (f a) r
linv-equiv₂'' f g p .a q | (a , b) , r , now | .b , s , now = trans≈ (bindD-input↓ g s) (p _ _ s)

linv-equiv₂ : {A B : Set}
  → (f : A → Delay B) (g : B → Delay A)
  → (∀ b a → f a ↓ b → g b ↓ a)
  → g ∙ f ∼ ⌊ f ⌋
linv-equiv₂ f g p x = ≈-equiv₂ (linv-equiv₂' _ _ p x , linv-equiv₂'' _ _ p x)

is-partial-inv-equiv₁ : {A B : Set} (f : A → Delay B)
  → is-partial-inv-rest f → is-partial-inv f
is-partial-inv-equiv₁ f (pinv-rest g α β) = pinv g (linv-equiv₁ g f α) (linv-equiv₁ f g β)

is-partial-inv-equiv₂ : {A B : Set} (f : A → Delay B)
  → is-partial-inv f → is-partial-inv-rest f
is-partial-inv-equiv₂ f (pinv g α β) = pinv-rest g (linv-equiv₂ g f α) (linv-equiv₂ f g β)

{-

postulate
  R1 : ∀ {A B} {f : A → Delay B} → f ∙ ⌊ f ⌋ ∼ f

  R2 : ∀ {A B C} {f : A → Delay B} {g : A → Delay C}
    → ⌊ f ⌋ ∙ ⌊ g ⌋ ∼ ⌊ g ⌋ ∙ ⌊ f ⌋
    
  R3 : ∀ {A B C} {f : A → Delay B}{g : A → Delay C}
    → ⌊ g ⌋ ∙ ⌊ f ⌋ ∼ ⌊ g ∙ ⌊ f ⌋ ⌋

  R4 : ∀ {A B C} {f : A → Delay B}{g : B → Delay C}
    → ⌊ g ⌋ ∙ f ∼ f ∙ ⌊ g ∙ f ⌋

-}
