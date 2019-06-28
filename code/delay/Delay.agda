{-# OPTIONS --without-K #-}

module delay.Delay where

open import Data.Product
open import Size
open import Relation.Binary.PropositionalEquality

-- The coinductive delay datatype

mutual
  data Delay' (i : Size) (A : Set) : Set where
    now : A → Delay' i A
    later : ∞Delay' i A → Delay' i A

  record ∞Delay' (i : Size) (A : Set) : Set where
    coinductive
    field force : {j : Size< i} → Delay' j A
open ∞Delay' public

Delay = Delay' ∞
∞Delay = ∞Delay' ∞

-- Non-terminating computation

mutual
  never : ∀ {i} {A} → Delay' i A
  never = later ∞never

  ∞never : ∀ {i} {A} → ∞Delay' i A
  force ∞never = never

-- Weak bisimilarity

mutual
  data [_]_≈'_ (i : Size) {A : Set} : (x y : Delay A) → Set where
    now : ∀ {x} → [ i ] now x ≈' now x
    later : ∀ {x y} → [ i ] force x ∞≈' force y → [ i ] later x ≈' later y
    laterL : ∀ {x y} → [ i ] force x ≈' y → [ i ] later x ≈' y
    laterR : ∀ {x y} → [ i ] x ≈' force y → [ i ] x ≈' later y

  record [_]_∞≈'_ (i : Size) {A : Set} (x y : Delay A) : Set where
    coinductive
    constructor wb
    field force : {j : Size< i} → [ j ] x ≈' y
open [_]_∞≈'_ public

_≈_ : {A : Set} → (x y : Delay A) → Set
x ≈ y = [ ∞ ] x ≈' y

_∞≈_ : {A : Set} → (x y : Delay A) → Set
x ∞≈ y = [ ∞ ] x ∞≈' y

-- Convergence

_↓_ : ∀ {A} → Delay A → A → Set
x ↓ a = x ≈ now a

-- Weak bisimilarity is an equivalence relation

mutual
  refl≈ : ∀ {i} {A} {x : Delay A} → [ i ] x ≈' x
  refl≈ {x = now x} = now
  refl≈ {x = later x} = later ∞refl≈

  ∞refl≈ : ∀ {i} {A} {x : Delay A} → [ i ] x ∞≈' x
  force ∞refl≈ = refl≈

mutual
  sym≈ : ∀ {i} {A} {x y : Delay A} → [ i ] x ≈' y → [ i ] y ≈' x
  sym≈ now = now
  sym≈ (later p) = later (∞sym≈ p)
  sym≈ (laterL p) = laterR (sym≈ p)
  sym≈ (laterR p) = laterL (sym≈ p)

  ∞sym≈ : ∀ {i} {A} {x y : Delay A} → [ i ] x ∞≈' y → [ i ] y ∞≈' x
  force (∞sym≈ p) = sym≈ (force p)

laterL-1 : ∀ {i} {j : Size< i} {A} {x} {y : Delay A}
  → [ i ] later x ≈' y → [ j ] force x ≈' y
laterL-1 (later p) = laterR (force p)
laterL-1 (laterL p) = p
laterL-1 (laterR p) = laterR (laterL-1 p)

laterR-1 : ∀ {i} {j : Size< i} {A} {x : Delay A} {y}
  → [ i ] x ≈' later y → [ j ] x ≈' force y
laterR-1 (later p) = laterL (force p)
laterR-1 (laterL p) = laterL (laterR-1 p)
laterR-1 (laterR p) = p  

later-1 : ∀ {i} {j : Size< i} {A} {x y : ∞Delay A} 
  → [ i ] later x ≈' later y → [ j ] force x ≈' force y
later-1 (later p) = force p
later-1 (laterL p) = laterR-1 p
later-1 (laterR p) = laterL-1 p  

trans≈-now : ∀ {i} {A} {x} {y z : Delay A} →
             [ i ] now x ≈' y → y ≈ z → [ i ] now x ≈' z
trans≈-now now q = q
trans≈-now (laterR p) (later q) = trans≈-now p (laterR (force q))
trans≈-now (laterR p) (laterL q) = trans≈-now p q
trans≈-now (laterR p) (laterR q) = laterR (trans≈-now p (laterL-1 q))             

mutual
  trans≈-later : ∀ {i} {A} {x} {y z : Delay A} →
                 later x ≈ y → y ≈ z → [ i ] later x ≈' z
  trans≈-later p now = p
  trans≈-later p (later q) = later λ { .force → trans≈ (later-1 p) (force q) }
  trans≈-later p (laterL q) = laterL (trans≈ (later-1 p) q)
  trans≈-later p (laterR q) = later λ { .force → trans≈ (laterL-1 p) q }

  trans≈ : ∀ {i} {A} {x y z : Delay A} → x ≈ y → y ≈ z → [ i ] x ≈' z
  trans≈ {x = now x} p q = trans≈-now p q
  trans≈ {x = later x} p q = trans≈-later p q

-- Equivalent specification of weak bisimilarity

≈-equiv₁ : ∀ {A} {x y : Delay A} → x ≈ y
  → ∀ {a} → x ↓ a → y ↓ a
≈-equiv₁ p now = sym≈ p
≈-equiv₁ p (laterL q) = ≈-equiv₁ (laterL-1 p) q

mutual
  ≈-equiv₂ : ∀ {A} {x y : Delay A} 
    → (∀ {a} → (x ↓ a → y ↓ a) × (y ↓ a → x ↓ a))
    → x ≈ y
  ≈-equiv₂ {x = now x} {y} p = sym≈ (proj₁ p now)
  ≈-equiv₂ {x = later x} {now y} p = proj₂ p now
  ≈-equiv₂ {x = later x} {later y} p =
    later (∞≈-equiv₂ {x = force x} {force y}
      ((λ q → laterL-1 (proj₁ p (laterL q))) , (λ q → laterL-1 (proj₂ p (laterL q)))))  

  ∞≈-equiv₂ : ∀ {A} {x y : Delay A} 
    → (∀ {a} → (x ↓ a → y ↓ a) × (y ↓ a → x ↓ a))
    → x ∞≈ y
  force (∞≈-equiv₂ p) = ≈-equiv₂ p

-- Unique convergence value

unique↓ : ∀ {A} {x : Delay A} {a a'}
  → x ↓ a → x ↓ a' → a ≡ a'
unique↓ now now = refl
unique↓ (laterL p) (laterL q) = unique↓ p q  

