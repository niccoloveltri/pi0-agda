{-# OPTIONS --without-K #-}

module pi0-syntax.Types where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Nat 
open import Data.Fin hiding (_≟_)

-- Types of Π₀

infix  31 _⊕_
infix  31 _⊗_

data Ty : ℕ → Set where
  var : ∀ {n} → Fin n → Ty n
  𝟘 𝟙 : ∀ {n} → Ty n
  _⊕_ _⊗_ : ∀ {n} → Ty n → Ty n → Ty n
  μ : ∀ {n} → Ty (suc n) → Ty n

wk : ∀ {n} → Ty n → Ty (suc n)
wk {n} (var i) = var (raise (suc zero) i)
wk 𝟘 = 𝟘
wk 𝟙 = 𝟙
wk (A ⊕ A') = (wk A) ⊕ (wk A')
wk (A ⊗ A') = (wk A) ⊗ (wk A')
wk (μ A) = μ (wk A)

sub : ∀ {n} → Ty (suc n) → Ty n → Ty n
sub {n} (var i) B with n ≟ toℕ i
sub {n} (var i) B | yes p = B
sub {n} (var i) B | no ¬p = var (lower₁ i ¬p)
sub 𝟘 B = 𝟘
sub 𝟙 B = 𝟙
sub (A ⊕ A') B = (sub A B) ⊕ (sub A' B)
sub (A ⊗ A') B = (sub A B) ⊗ (sub A' B)
sub (μ A) B = μ (sub A (wk B))




