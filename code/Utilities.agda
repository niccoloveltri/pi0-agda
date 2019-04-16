{-# OPTIONS --without-K #-}

module Utilities where

open import Data.Empty
open import Data.Sum renaming (map to map⊎; swap to swap⊎)
open import Data.Unit
open import Data.Product renaming (map to map×; swap to swap×)
open import Relation.Binary.PropositionalEquality hiding (naturality)
open import Function

record is-total-inv {A B : Set} (f : A → B) : Set where
  constructor tinv
  field
    g : B → A
    α : ∀ x → f (g x) ≡ x
    β : ∀ x → g (f x) ≡ x

_≅_ : Set → Set → Set
A ≅ B = Σ (A → B) is-total-inv

id≅ : ∀ {A} → A ≅ A
id≅ = id , tinv id (λ _ → refl) (λ _ → refl)

_∘≅_ : ∀ {A B C} → B ≅ C → A ≅ B → A ≅ C
(g , tinv g-1 p q) ∘≅ (f , tinv f-1 p' q') = g ∘ f , tinv (f-1 ∘ g-1) (λ _ → trans (cong g (p' _)) (p _))
                                                                      (λ _ → trans (cong f-1 (q _)) (q' _))

_-1≅ : ∀ {A B} → A ≅ B → B ≅ A
(f , tinv f-1 p q) -1≅ = f-1 , tinv f q p

map⊎≅ : {A B C D : Set} → A ≅ B → C ≅ D → (A ⊎ C) ≅ (B ⊎ D)
map⊎≅ (f , tinv f-1 p q) (g , tinv g-1 p' q') = (map⊎ f g) , tinv (map⊎ f-1 g-1) (λ { (inj₁ x) → cong inj₁ (p x) ; (inj₂ y) → cong inj₂ (p' y) })
                                                                                 (λ { (inj₁ x) → cong inj₁ (q x) ; (inj₂ y) → cong inj₂ (q' y) })

map×≅ : {A B C D : Set} → A ≅ B → C ≅ D → (A × C) ≅ (B × D)
map×≅ (f , tinv f-1 p q) (g , tinv g-1 p' q') = (map× f g) , tinv (map× f-1 g-1) (λ { (x , y) → cong₂ _,_ (p x) (p' y) })
                                                                                 (λ { (x , y) → cong₂ _,_ (q x) (q' y) })

λ⊎ : {A : Set} → ⊥ ⊎ A → A
λ⊎ (inj₂ y) = y

λ⊎-1 : {A : Set} → A → ⊥ ⊎ A
λ⊎-1 = inj₂

λ⊎≅ : ∀ {A} → (⊥ ⊎ A) ≅ A
λ⊎≅ = λ⊎ , tinv λ⊎-1 (λ _ → refl) (λ { (inj₂ _) → refl })

swap⊎≅ : ∀ {A B} → (A ⊎ B) ≅ (B ⊎ A)
swap⊎≅ = swap⊎ , tinv swap⊎ (λ { (inj₁ x) → refl ; (inj₂ y) → refl }) 
                            (λ { (inj₁ x) → refl ; (inj₂ y) → refl })

α⊎ : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
α⊎ (inj₁ (inj₁ x)) = inj₁ x
α⊎ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
α⊎ (inj₂ y) = inj₂ (inj₂ y)

α⊎-1 : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
α⊎-1 (inj₁ x) = inj₁ (inj₁ x)
α⊎-1 (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
α⊎-1 (inj₂ (inj₂ y)) = inj₂ y


α⊎≅ : {A B C : Set} → ((A ⊎ B) ⊎ C) ≅ (A ⊎ (B ⊎ C))
α⊎≅ = α⊎ , tinv α⊎-1 (λ { (inj₁ x) → refl ; (inj₂ (inj₁ y)) → refl ; (inj₂ (inj₂ y)) → refl })
                     (λ { (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ y) → refl })
                     
ρ⊎≅ : {A : Set} → A ≅ (A ⊎ ⊥)
ρ⊎≅ = swap⊎≅ ∘≅ (λ⊎≅ -1≅)

ρ⊎ : {A : Set} → A → A ⊎ ⊥
ρ⊎ = proj₁ ρ⊎≅ 

ρ⊎-1 : {A : Set} → A ⊎ ⊥ → A
ρ⊎-1 = is-total-inv.g (proj₂ ρ⊎≅)

λ× : {A : Set} → ⊤ × A → A
λ× (_ , x) = x

λ×-1 : {A : Set} → A → ⊤ × A
λ×-1 x = tt , x

λ×≅ : ∀ {A} → (⊤ × A) ≅ A
λ×≅ = λ× , tinv λ×-1 (λ _ → refl) (λ { (_ , _) → refl })

swap×≅ : ∀ {A B} → (A × B) ≅ (B × A)
swap×≅ = swap× , tinv swap× (λ { (_ , _) → refl }) (λ { (_ , _) → refl })

α× : {A B C : Set} → ((A × B) × C) → (A × (B × C))
α× ((x , y) , z) = (x , y , z)

α×-1 : {A B C : Set} → (A × (B × C)) → ((A × B) × C)
α×-1 (x , y , z) = (x , y) , z

α×≅ : ∀ {A B C} → ((A × B) × C) ≅ (A × (B × C))
α×≅ = α× , tinv α×-1 (λ { (x , y , z) → refl }) (λ { ((x , y) , z) → refl })

ρ×≅ : {A : Set} → A ≅ (A × ⊤)
ρ×≅ = swap×≅ ∘≅ (λ×≅ -1≅)

ρ× : {A : Set} → A → A × ⊤
ρ× = proj₁ ρ×≅ 

ρ×-1 : {A : Set} → A × ⊤ → A
ρ×-1 = is-total-inv.g (proj₂ ρ×≅)

κL× : {A : Set} → ⊥ × A → ⊥
κL× (() , _)

κL×-1 : {A : Set} → ⊥ → ⊥ × A
κL×-1 ()

κL×≅ : {A : Set} → (⊥ × A) ≅ ⊥
κL×≅ = κL× , tinv κL×-1 (λ { () }) (λ { (() , y) })

κR×≅ : {A : Set} → (A × ⊥) ≅ ⊥
κR×≅ = κL×≅ ∘≅ swap×≅

κR× : {A : Set} → A × ⊥ → ⊥
κR× = proj₁ κR×≅

κR×-1 : {A : Set} → ⊥ → A × ⊥
κR×-1 = is-total-inv.g (proj₂ κR×≅)

δR×⊎ : {A B C : Set} → ((A ⊎ B) × C) → (A × C ⊎ B × C)
δR×⊎ (inj₁ x , z) = inj₁ (x , z)
δR×⊎ (inj₂ y , z) = inj₂ (y , z)

δR×⊎-1 : {A B C : Set} → (A × C ⊎ B × C) → ((A ⊎ B) × C)
δR×⊎-1 (inj₁ (x , y)) = inj₁ x , y
δR×⊎-1 (inj₂ (x , y)) = inj₂ x , y

δR×⊎≅ : ∀ {A B C} → ((A ⊎ B) × C) ≅ (A × C ⊎ B × C)
δR×⊎≅ = δR×⊎ , tinv δR×⊎-1 (λ { (inj₁ (x , y)) → refl ; (inj₂ (x , y)) → refl })
                           (λ { (inj₁ x , y) → refl ; (inj₂ x , y) → refl })

δL×⊎≅ : ∀ {A B C} → (A × (B ⊎ C)) ≅ (A × B ⊎ A × C)
δL×⊎≅ = (map⊎≅ swap×≅ swap×≅ ∘≅ δR×⊎≅) ∘≅ swap×≅

δL×⊎ : {A B C : Set} → (A × (B ⊎ C)) → (A × B ⊎ A × C)
δL×⊎ = proj₁ δL×⊎≅

δL×⊎-1 : {A B C : Set} → (A × B ⊎ A × C) → (A × (B ⊎ C)) 
δL×⊎-1 = is-total-inv.g (proj₂ δL×⊎≅)

I≅ : {A B C : Set} (x : A × (B ⊎ C)) → swap⊎ (δL×⊎ x) ≡ δL×⊎ (map× id swap⊎ x) 
I≅ (x , inj₁ y) = refl
I≅ (x , inj₂ y) = refl

