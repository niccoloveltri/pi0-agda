{-# OPTIONS --without-K #-}

module pi0-semantics.1Programs where

open import Data.Empty
open import Data.Sum renaming (map to map⊎; swap to swap⊎)
open import Data.Unit
open import Data.Product renaming (map to map×; swap to swap×)
open import Relation.Binary.PropositionalEquality hiding (naturality)
open import Function
open import Data.Nat
open import Data.Fin hiding (fold)

open import Utilities
open import pi0-syntax.Types
open import pi0-syntax.1Programs
open import pi0-semantics.Types

open import delay.Delay
open import delay.Monad
open import delay.Elgot
open import delay.PartialInv
open import delay.Structure

-- Intepretation of terms

fold≅ : ∀ {n} {A : Ty (suc n)} {ρ : Fin n → Set} → sem-Ty ρ (sub A (μ A)) ≅ sem-μ ρ A
fold≅ = sup , tinv (λ { (sup x) → x }) (λ { (sup x) → refl }) (λ _ → refl)

sem-⟷ : ∀ {n} (ρ : Fin n → Set) {A B : Ty n}
  → A ⟷ B → sem-Ty ρ A ≃₁ sem-Ty ρ B
sem-⟷ ρ id⟷ = ≅-to-≃₁ id≅
sem-⟷ ρ λ⊕ = ≅-to-≃₁ λ⊎≅
sem-⟷ ρ λ⊕-1 = ≅-to-≃₁ (λ⊎≅ -1≅)
sem-⟷ ρ α⊕ = ≅-to-≃₁ α⊎≅
sem-⟷ ρ α⊕-1 = ≅-to-≃₁ (α⊎≅ -1≅)
sem-⟷ ρ s⊕ = ≅-to-≃₁ swap⊎≅
sem-⟷ ρ λ⊗ = ≅-to-≃₁ λ×≅
sem-⟷ ρ λ⊗-1 = ≅-to-≃₁ (λ×≅ -1≅)
sem-⟷ ρ α⊗ = ≅-to-≃₁ α×≅
sem-⟷ ρ α⊗-1 = ≅-to-≃₁ (α×≅ -1≅)
sem-⟷ ρ s⊗ = ≅-to-≃₁ swap×≅
sem-⟷ ρ κL = ≅-to-≃₁ κL×≅
sem-⟷ ρ κL-1 = ≅-to-≃₁ (κL×≅ -1≅)
sem-⟷ ρ δR = ≅-to-≃₁ δR×⊎≅
sem-⟷ ρ δR-1 = ≅-to-≃₁ (δR×⊎≅ -1≅)
sem-⟷ ρ (f ⊙ g) = (sem-⟷ ρ f) ⊙≃₁ (sem-⟷ ρ g)
sem-⟷ ρ (f ⊕ g) = (sem-⟷ ρ f) ⊕≃₁ (sem-⟷ ρ g)
sem-⟷ ρ (f ⊗ g) = (sem-⟷ ρ f) ⊗≃₁ (sem-⟷ ρ g)
sem-⟷ ρ fold = ≅-to-≃₁ fold≅
sem-⟷ ρ unfold = ≅-to-≃₁ (fold≅ -1≅)
sem-⟷ ρ (trace f) = trace≃₁ (sem-⟷ ρ f)


