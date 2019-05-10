{-# OPTIONS --without-K #-}

module pi0-semantics.Types where

open import Data.Empty
open import Data.Sum renaming (map to map⊎; swap to swap⊎)
open import Data.Unit
open import Data.Product renaming (map to map×; swap to swap×)
open import Relation.Binary.PropositionalEquality hiding (naturality)
open import Function
open import Data.Nat
open import Data.Fin

open import Utilities
open import pi0-syntax.Types

-- Semantic types

sem-Ty : ∀ {n} → (Fin n → Set) → Ty n → Set
data sem-μ {n : ℕ} (ρ : Fin n → Set) : Ty (suc n) → Set 

sem-Ty ρ (var i) = ρ i
sem-Ty ρ 𝟘 = ⊥
sem-Ty ρ 𝟙 = ⊤
sem-Ty ρ (A ⊕ A') = (sem-Ty ρ A) ⊎ (sem-Ty ρ A')
sem-Ty ρ (A ⊗ A') = (sem-Ty ρ A) × (sem-Ty ρ A')
sem-Ty ρ (μ A) = sem-μ ρ A

data sem-μ ρ where
  sup : ∀ {A} → sem-Ty ρ (sub A (μ A)) → sem-μ ρ A 

