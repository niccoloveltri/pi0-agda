{-# OPTIONS --without-K #-}

module pi0-syntax.2Programs where

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Fin hiding (fold)

open import pi0-syntax.Types
open import pi0-syntax.1Programs

-- Program equivalences of Π₀

infix 30 _⟺_

data _⟺_ : {n : ℕ} {A B : Ty n} → A ⟷ B → A ⟷ B → Set where

-- Equivalence laws
  id⟺ : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⟺ f
  trans⟺ : ∀ {n} {A B : Ty n} {f g h :  A ⟷ B} → g ⟺ h → f ⟺ g → f ⟺ h

-- Congruence laws
  _⊙_ : ∀ {n} {A B C : Ty n} {f g :  A ⟷ B} {f' g' :  B ⟷ C}
    → f' ⟺ g' → f ⟺ g → f' ⊙ f ⟺ g' ⊙ g
  _⊕_ : ∀ {n} {A B C D : Ty n} {f g :  A ⟷ B} {f' g' :  C ⟷ D}
    → f ⟺ g → f' ⟺ g' → f ⊕ f' ⟺ g ⊕ g'
  _⊗_ : ∀ {n} {A B C D : Ty n} {f g :  A ⟷ B} {f' g' :  C ⟷ D}
    → f ⟺ g → f' ⟺ g' → f ⊗ f' ⟺ g ⊗ g'

-- Category laws
  lid : ∀ {n} {A B : Ty n} {f : A ⟷ B} → id⟷ ⊙ f ⟺ f
  rid : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⊙ id⟷ ⟺ f
  ass : ∀ {n} {A B C D : Ty n} {f : A ⟷ B} {g : B ⟷ C} {h : C ⟷ D}
    → h ⊙ (g ⊙ f) ⟺ (h ⊙ g) ⊙ f

-- Inverse category laws
  inve : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⊙ dagger f ⊙ f ⟺ f
  invu : ∀ {n} {A B C : Ty n} {f : A ⟷ B} {g : C ⟷ B}
    → f ⊙ dagger f ⊙ g ⊙ dagger g ⟺ g ⊙ dagger g ⊙ f ⊙ dagger f
  
-- ⊕ functorial
  fun⊕id : ∀ {n} {A B : Ty n} → id⟷ ⊕ id⟷ ⟺ id⟷ {A = A ⊕ B}
  fun⊕⊙ : ∀ {n} {A B C D E F : Ty n}
    → {f : A ⟷ B} {g : B ⟷ C} {h : D ⟷ E} {k : E ⟷ F}
    → (g ⊙ f) ⊕ (k ⊙ h) ⟺ (g ⊕ k) ⊙ (f ⊕ h)

-- ⊗ functorial
  fun⊗id : ∀ {n} {A B : Ty n} → id⟷ ⊗ id⟷ ⟺ id⟷ {A = A ⊗ B}
  fun⊗⊙ : ∀ {n} {A B C D E F : Ty n}
    → {f : A ⟷ B} {g : B ⟷ C} {h : D ⟷ E} {k : E ⟷ F}
    → (g ⊙ f) ⊗ (k ⊙ h) ⟺ (g ⊗ k) ⊙ (f ⊗ h)

-- λ⊕, α⊕ and s⊕ natural
  nλ⊕ : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⊙ λ⊕ ⟺ λ⊕ ⊙ (id⟷ ⊕ f)
  nα⊕ : ∀ {n} {A B C D E F : Ty n} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → (f ⊕ (g ⊕ h)) ⊙ α⊕ ⟺ α⊕ ⊙ ((f ⊕ g) ⊕ h)
  ns⊕ : ∀ {n} {A B C D : Ty n} {f : A ⟷ B} {g : C ⟷ D} 
    → (f ⊕ g) ⊙ s⊕ ⟺ s⊕ ⊙ (g ⊕ f)

-- λ⊗, α⊗ and s⊗ natural
  nλ⊗ : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⊙ λ⊗ ⟺ λ⊗ ⊙ (id⟷ ⊗ f)
  nα⊗ : ∀ {n} {A B C D E F : Ty n} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → (f ⊗ (g ⊗ h)) ⊙ α⊗ ⟺ α⊗ ⊙ ((f ⊗ g) ⊗ h)
  ns⊗ : ∀ {n} {A B C D : Ty n} {f : A ⟷ B} {g : C ⟷ D} 
    → (f ⊗ g) ⊙ s⊗ ⟺ s⊗ ⊙ (g ⊗ f)

-- κL and δR natural
  nκL : ∀ {n} {A B : Ty n} {f : A ⟷ B} → κL ⊙ (id⟷ ⊗ f) ⟺ κL
  nδR : ∀ {n} {A B C D E F : Ty n} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → ((f ⊗ h) ⊕ (g ⊗ h)) ⊙ δR ⟺ δR ⊙ ((f ⊕ g) ⊗ h)

-- ⊕ symmetric monoidal
  ραλ⊕ : ∀ {n} {A B : Ty n} →  ρ⊕-1 ⊕ id⟷ ⟺ (id⟷ ⊕ λ⊕) ⊙ α⊕ {A = A} {𝟘} {B}
  ααα⊕ : ∀ {n} {A B C D : Ty n}
    → α⊕ ⊙ α⊕ {A = A ⊕ B} {C} {D} ⟺ (id⟷ ⊕ α⊕) ⊙ α⊕ ⊙ (α⊕ ⊕ id⟷)
  ρsλ⊕ : ∀ {n} {A : Ty n} → ρ⊕-1 {A = A} ⟺ λ⊕ ⊙ s⊕
  ss⊕ : ∀ {n} {A B : Ty n} → s⊕ ⊙ s⊕ ⟺ id⟷ {A = A ⊕ B}
  sα⊕ : ∀ {n} {A B C : Ty n} 
    → α⊕ ⊙ s⊕ ⊙ α⊕ {A = A} {B} {C} ⟺ (id⟷ ⊕ s⊕) ⊙ α⊕ ⊙ (s⊕ ⊕ id⟷)

-- ⊗ symmetric monoidal
  ραλ⊗ : ∀ {n} {A B : Ty n} → ρ⊗-1 ⊗ id⟷ ⟺ (id⟷ ⊗ λ⊗) ⊙ α⊗ {A = A} {𝟙} {B}
  ααα⊗ : ∀ {n} {A B C D : Ty n}
    → α⊗ ⊙ α⊗ {A = A ⊗ B} {C} {D} ⟺ (id⟷ ⊗ α⊗) ⊙ α⊗ ⊙ (α⊗ ⊗ id⟷)
  ρsλ⊗ : ∀ {n} {A : Ty n} → ρ⊗-1 {A = A} ⟺ λ⊗ ⊙ s⊗
  ss⊗ : ∀ {n} {A B : Ty n} → s⊗ ⊙ s⊗ ⟺ id⟷ {A = A ⊗ B}
  sα⊗ : ∀ {n} {A B C : Ty n}
    → α⊗ ⊙ s⊗ ⊙ α⊗ {A = A} {B} {C} ⟺ (id⟷ ⊗ s⊗) ⊙ α⊗ ⊙ (s⊗ ⊗ id⟷)

-- Laplaza's coherence equations for rig categories
  I : ∀ {n} {A B C : Ty n} → s⊕ ⊙ δL {A = A} {B} {C} ⟺ δL ⊙ (id⟷ ⊗ s⊕)
  II : ∀ {n} {A B C : Ty n} → (s⊗ ⊕ s⊗) ⊙ δR {A = A} {B} {C} ⟺ δL ⊙ s⊗
  III :  ∀ {n} {A B C : Ty n} → s⊕ ⊙ δR {A = A} {B} {C} ⟺ δR ⊙ (s⊕ ⊗ id⟷)
  IV : ∀ {n} {A B C D : Ty n}
    → α⊕-1 ⊙ (id⟷ ⊕ δR) ⊙ δR {A = A} {B ⊕ C} {D} ⟺ (δR ⊕ id⟷) ⊙ δR ⊙ (α⊕-1 ⊗ id⟷)
  V : ∀ {n} {A B C D : Ty n}
    → α⊕-1 ⊙ (id⟷ ⊕ δL) ⊙ δL {A = A} {B} {C ⊕ D} ⟺ (δL ⊕ id⟷) ⊙ δL ⊙ (id⟷ ⊗ α⊕-1)
  VI : ∀ {n} {A B C D : Ty n}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δL ⊙ (id⟷ ⊗ δL) ⟺ δL ⊙ α⊗-1 {A = A} {B} {C ⊕ D}
  VII : ∀ {n} {A B C D : Ty n}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δR {A = A} {B} {C ⊗ D} ⟺ δR ⊙ (δR ⊗ id⟷) ⊙ α⊗-1
  VIII : ∀ {n} {A B C D : Ty n}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δL ⊙ (id⟷ ⊗ δR) ⟺ δR ⊙ (δL ⊗ id⟷) ⊙ α⊗-1 {A = A} {B ⊕ C} {D}
  IX : ∀ {n} {A B C D : Ty n}
    → (α⊕-1 ⊕ id⟷) ⊙ ((id⟷ ⊕ s⊕) ⊕ id⟷) ⊙ (α⊕ ⊕ id⟷) ⊙ α⊕-1 ⊙ (δL ⊕ δL) ⊙ δR ⟺
      α⊕-1 ⊙ (δR ⊕ δR) ⊙ δL {A = A ⊕ B} {C} {D}
  X : ∀ {n} → κL {n} {𝟘} ⟺ κR
  XI : ∀ {n} {A B : Ty n} → κL {A = A ⊕ B} ⟺ λ⊕ ⊙ (κL ⊕ κL) ⊙ δL
  XII : ∀ {n} {A B : Ty n} → κR {A = A ⊕ B} ⟺ λ⊕ ⊙ (κR ⊕ κR) ⊙ δR
  XIII : ∀ {n} → ρ⊗-1 {n} {𝟘} ⟺ κL
  XIV : ∀ {n} → λ⊗ {n} {𝟘} ⟺ κR
  XV : ∀ {n} {A : Ty n} → κR {A = A} ⟺ κL ⊙ s⊗
  XVI : ∀ {n} {A B : Ty n} → κL {A = A ⊗ B} ⟺ κL ⊙ (κL ⊗ id⟷) ⊙ α⊗-1
  XVII : ∀ {n} {A B : Ty n} → κR ⊙ (id⟷ ⊗ κL) ⟺ κL ⊙ (κR ⊗ id⟷) ⊙ α⊗-1 {A = A} {𝟘} {B}
  XVIII : ∀ {n} {A B : Ty n} → κR ⊙ α⊗-1 {A = A} {B} {𝟘} ⟺ κR ⊙ (id⟷ ⊗ κR)
  XIX : ∀ {n} {A B : Ty n} → id⟷ ⊗ λ⊕ ⟺ λ⊕ ⊙ (κR ⊕ id⟷) ⊙ δL {A = A} {𝟘} {B}
  XX : ∀ {n} {A B : Ty n} → λ⊕ ⊙ (κL ⊕ id⟷) ⊙ δR {A = 𝟘} {A} {B} ⟺ λ⊕ ⊗ id⟷
  XXI : ∀ {n} {A B : Ty n} → ρ⊕-1 ⊙ (id⟷ ⊕ κR) ⊙ δL {A = A} {B} {𝟘} ⟺ id⟷ ⊗ ρ⊕-1
  XXII : ∀ {n} {A B : Ty n} → ρ⊕-1 ⊙ (id⟷ ⊕ κL) ⊙ δR {A = A} {𝟘} {B} ⟺ ρ⊕-1 ⊗ id⟷
  XXIII : ∀ {n} {A B : Ty n} → λ⊗ {A = A ⊕ B} ⟺ (λ⊗ ⊕ λ⊗) ⊙ δL
  XXIV : ∀ {n} {A B : Ty n} → ρ⊗-1 {A = A ⊕ B} ⟺ (ρ⊗-1 ⊕ ρ⊗-1) ⊙ δR

-- Trace axioms
  naturalityL : ∀ {n} {A B C D : Ty n} {f : C ⟷ D} {g : A ⊕ B ⟷ A ⊕ C}
    → f ⊙ trace g ⟺ trace ((id⟷ ⊕ f) ⊙ g)
  naturalityR : ∀ {n} {A B C D : Ty n} {f : B ⟷ C} {g : A ⊕ C ⟷ A ⊕ D}
    → trace g ⊙ f ⟺ trace (g ⊙ (id⟷ ⊕ f))
  dinaturality : ∀ {n} {A B C D : Ty n} {f : B ⟷ A} {g : A ⊕ C ⟷ B ⊕ D}
    → trace ((f ⊕ id⟷) ⊙ g) ⟺ trace (g ⊙ (f ⊕ id⟷))
  superposing : ∀ {n} {A B C D : Ty n} {f : A ⊕ B ⟷ A ⊕ C}
    → trace (α⊕ ⊙ (f ⊕ id⟷) ⊙ α⊕-1) ⟺ trace f ⊕ id⟷ {A = D} 
  vanishingI : ∀ {n} {A B : Ty n} {f : 𝟘 ⊕ A ⟷ 𝟘 ⊕ B} → f ⟺ λ⊕-1 ⊙ trace f ⊙ λ⊕ 
  vanishingII : ∀ {n} {A B C D : Ty n} {f : (A ⊕ B) ⊕ C ⟷ (A ⊕ B) ⊕ D}
    → trace f ⟺ trace (trace (α⊕ ⊙ f ⊙ α⊕-1))
  yanking : ∀ {n} {A : Ty n} → trace s⊕ ⟺ id⟷ {A = A}

{-
inve' : ∀ {n} {A B : Ty n} {f : A ⟷ B} → f ⊙ dagger f ⊙ f ⟺ f
inve' {f = id⟷} = {!!}
inve' {f = λ⊕} = {!!}
inve' {f = λ⊕-1} = {!!}
inve' {f = α⊕} = {!!}
inve' {f = α⊕-1} = {!!}
inve' {f = s⊕} = {!!}
inve' {f = λ⊗} = {!!}
inve' {f = λ⊗-1} = {!!}
inve' {f = α⊗} = {!!}
inve' {f = α⊗-1} = {!!}
inve' {f = s⊗} = {!!}
inve' {f = κL} = {!!}
inve' {f = κL-1} = {!!}
inve' {f = δR} = {!!}
inve' {f = δR-1} = {!!}
inve' {f = f ⊙ f₁} = {!!}
inve' {f = f ⊕ f₁} = {!!}
inve' {f = f ⊗ f₁} = {!!}
inve' {f = fold} = {!!}
inve' {f = unfold} = {!!}
inve' {f = trace f} = {!!}
-}
