{-# OPTIONS --without-K #-}

module pi0-syntax.1Programs where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (fold)

open import pi0-syntax.Types

-- Terms of Π₀

infix 30 _⟷_
infixl 31 _⊙_

data _⟷_ {n : ℕ} : Ty n → Ty n → Set where
  id⟷ : ∀ {A} → A ⟷ A
  
  λ⊕ : ∀ {A} → 𝟘 ⊕ A ⟷ A
  λ⊕-1 : ∀ {A} → A ⟷ 𝟘 ⊕ A
  α⊕ : ∀ {A B C} → (A ⊕ B) ⊕ C ⟷ A ⊕ (B ⊕ C)
  α⊕-1 : ∀ {A B C} → A ⊕ (B ⊕ C) ⟷ (A ⊕ B) ⊕ C
  s⊕ : ∀ {A B} → A ⊕ B ⟷ B ⊕ A
  
  λ⊗ : ∀ {A} → 𝟙 ⊗ A ⟷ A
  λ⊗-1 : ∀ {A} → A ⟷ 𝟙 ⊗ A
  α⊗ : ∀ {A B C} → (A ⊗ B) ⊗ C ⟷ A ⊗ (B ⊗ C)
  α⊗-1 : ∀ {A B C} → A ⊗ (B ⊗ C) ⟷ (A ⊗ B) ⊗ C
  s⊗ : ∀ {A B} → A ⊗ B ⟷ B ⊗ A

  κL : ∀ {A} → 𝟘 ⊗ A ⟷ 𝟘
  κL-1 : ∀ {A} → 𝟘 ⟷ 𝟘 ⊗ A
  δR : ∀ {A B C} → (A ⊕ B) ⊗ C ⟷ (A ⊗ C) ⊕ (B ⊗ C) 
  δR-1 : ∀ {A B C} → (A ⊗ C) ⊕ (B ⊗ C) ⟷ (A ⊕ B) ⊗ C

  _⊙_ : ∀ {A B C} → B ⟷ C → A ⟷ B → A ⟷ C 
  _⊕_ : ∀ {A B C D} → A ⟷ B → C ⟷ D → A ⊕ C ⟷ B ⊕ D
  _⊗_ : ∀ {A B C D} → A ⟷ B → C ⟷ D → A ⊗ C ⟷ B ⊗ D

  fold : ∀ {A} → sub A (μ A) ⟷ μ A
  unfold : ∀ {A} → μ A ⟷ sub A (μ A)

  trace : ∀ {A B C} → A ⊕ B ⟷ A ⊕ C → B ⟷ C

ρ⊕ : ∀ {n} {A : Ty n} → A ⟷ A ⊕ 𝟘
ρ⊕ = s⊕ ⊙ λ⊕-1

ρ⊗ : ∀ {n} {A : Ty n} → A ⟷ A ⊗ 𝟙
ρ⊗ = s⊗ ⊙ λ⊗-1

κR : ∀ {n} {A : Ty n} → A ⊗ 𝟘 ⟷ 𝟘
κR = κL ⊙ s⊗

δL : ∀ {n} {A B C : Ty n} → A ⊗ (B ⊕ C) ⟷ (A ⊗ B) ⊕ (A ⊗ C) 
δL = (s⊗ ⊕ s⊗) ⊙ δR ⊙ s⊗ 

dagger : ∀ {n} {A B : Ty n} → A ⟷ B → B ⟷ A
dagger id⟷ = id⟷
dagger λ⊕ = λ⊕-1
dagger λ⊕-1 = λ⊕
dagger s⊕ = s⊕
dagger α⊕ = α⊕-1
dagger α⊕-1 = α⊕
dagger λ⊗ = λ⊗-1
dagger λ⊗-1 = λ⊗
dagger s⊗ = s⊗
dagger α⊗ = α⊗-1
dagger α⊗-1 = α⊗
dagger κL = κL-1
dagger κL-1 = κL
dagger δR = δR-1
dagger δR-1 = δR
dagger (f ⊙ g) = dagger g ⊙ dagger f
dagger (f ⊕ g) = dagger f ⊕ dagger g
dagger (f ⊗ g) = dagger f ⊗ dagger g
dagger fold = unfold
dagger unfold = fold
dagger (trace f) = trace (dagger f)

ρ⊕-1 : ∀ {n} {A : Ty n} → A ⊕ 𝟘 ⟷ A
ρ⊕-1 = dagger ρ⊕

ρ⊗-1 : ∀ {n} {A : Ty n} → A ⊗ 𝟙 ⟷ A
ρ⊗-1 = dagger ρ⊗

κR-1 : ∀ {n} {A : Ty n} → 𝟘 ⟷ A ⊗ 𝟘
κR-1 = dagger κR

δL-1 : ∀ {n} {A B C : Ty n} → (A ⊗ B) ⊕ (A ⊗ C) ⟷ A ⊗ (B ⊕ C)
δL-1 = dagger δL

dagger-dagger : ∀ {n} {A B : Ty n} (f : A ⟷ B) → dagger (dagger f) ≡ f
dagger-dagger id⟷ = refl
dagger-dagger λ⊕ = refl
dagger-dagger λ⊕-1 = refl
dagger-dagger α⊕ = refl
dagger-dagger α⊕-1 = refl
dagger-dagger s⊕ = refl
dagger-dagger λ⊗ = refl
dagger-dagger λ⊗-1 = refl
dagger-dagger α⊗ = refl
dagger-dagger α⊗-1 = refl
dagger-dagger s⊗ = refl
dagger-dagger κL = refl
dagger-dagger κL-1 = refl
dagger-dagger δR = refl
dagger-dagger δR-1 = refl
dagger-dagger (f ⊙ f₁) = cong₂ _⊙_ (dagger-dagger f) (dagger-dagger f₁)
dagger-dagger (f ⊕ f₁) = cong₂ _⊕_ (dagger-dagger f) (dagger-dagger f₁)
dagger-dagger (f ⊗ f₁) = cong₂ _⊗_ (dagger-dagger f) (dagger-dagger f₁)
dagger-dagger fold = refl
dagger-dagger unfold = refl
dagger-dagger (trace f) = cong trace (dagger-dagger f)


