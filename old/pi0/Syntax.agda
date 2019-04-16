{-# OPTIONS --without-K #-}

module pi0.Syntax where

open import Relation.Binary.PropositionalEquality

-- Types of Π₀

infix  31 _⊕_
infix  31 _⊗_

mutual
  data U : Set where
    𝟘 𝟙 : U
    _⊕_ _⊗_ : U → U → U
    μ : Code → U

  data Code : Set where
    ℂ : U → Code
    𝕀 : Code
    _⊕_ _⊗_ : Code → Code → Code

decode : Code → U → U
decode (ℂ A) _ = A
decode 𝕀 A = A
decode (F ⊕ G) A = decode F A ⊕ decode G A
decode (F ⊗ G) A = decode F A ⊗ decode G A


-- Programs of Π₀

infix 30 _⟷_
infixl 31 _⊙_

data _⟷_ : U → U → Set where
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

  fold : ∀ F → decode F (μ F) ⟷ μ F
  unfold : ∀ F → μ F ⟷ decode F (μ F)

  trace : ∀ {A B C} → A ⊕ B ⟷ A ⊕ C → B ⟷ C

ρ⊕ : ∀ {A} → A ⟷ A ⊕ 𝟘
ρ⊕ = s⊕ ⊙ λ⊕-1

ρ⊗ : ∀ {A} → A ⟷ A ⊗ 𝟙
ρ⊗ = s⊗ ⊙ λ⊗-1

κR : ∀ {A} → A ⊗ 𝟘 ⟷ 𝟘
κR = κL ⊙ s⊗

δL : ∀ {A B C} → A ⊗ (B ⊕ C) ⟷ (A ⊗ B) ⊕ (A ⊗ C) 
δL = (s⊗ ⊕ s⊗) ⊙ δR ⊙ s⊗ 

dagger : ∀ {A B} → A ⟷ B → B ⟷ A
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
dagger (fold F) = unfold F
dagger (unfold F) = fold F
dagger (trace f) = trace (dagger f)

dagger-dagger : ∀ {A B} (f : A ⟷ B) → dagger (dagger f) ≡ f
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
dagger-dagger (fold F) = refl
dagger-dagger (unfold F) = refl
dagger-dagger (trace f) = cong trace (dagger-dagger f)

ρ⊕-1 : ∀ {A} → A ⊕ 𝟘 ⟷ A
ρ⊕-1 = dagger ρ⊕

ρ⊗-1 : ∀ {A} → A ⊗ 𝟙 ⟷ A
ρ⊗-1 = dagger ρ⊗

κR-1 : ∀ {A} → 𝟘 ⟷ A ⊗ 𝟘
κR-1 = dagger κR

δL-1 : ∀ {A B C} → (A ⊗ B) ⊕ (A ⊗ C) ⟷ A ⊗ (B ⊕ C)
δL-1 = dagger δL

-- Program equivalences of Π₀

infix 30 _⟺_

data _⟺_ : {A B : U} → A ⟷ B → A ⟷ B → Set where

-- Equivalence laws
  id⟺ : ∀ {A B} {f : A ⟷ B} → f ⟺ f
  trans⟺ : ∀ {A B} {f g h :  A ⟷ B} → g ⟺ h → f ⟺ g → f ⟺ h

-- Congruence laws
  _⊙_ : ∀ {A B C} {f g :  A ⟷ B} {f' g' :  B ⟷ C}
    → f' ⟺ g' → f ⟺ g → f' ⊙ f ⟺ g' ⊙ g
  _⊕_ : ∀ {A B C D} {f g :  A ⟷ B} {f' g' :  C ⟷ D}
    → f ⟺ g → f' ⟺ g' → f ⊕ f' ⟺ g ⊕ g'
  _⊗_ : ∀ {A B C D} {f g :  A ⟷ B} {f' g' :  C ⟷ D}
    → f ⟺ g → f' ⟺ g' → f ⊗ f' ⟺ g ⊗ g'

-- Category laws
  lid : ∀ {A B} {f : A ⟷ B} → id⟷ ⊙ f ⟺ f
  rid : ∀ {A B} {f : A ⟷ B} → f ⊙ id⟷ ⟺ f
  ass : ∀ {A B C D} {f : A ⟷ B} {g : B ⟷ C} {h : C ⟷ D}
    → h ⊙ (g ⊙ f) ⟺ (h ⊙ g) ⊙ f

-- Inverse category laws
  inve : ∀ {A B} {f : A ⟷ B} → f ⊙ dagger f ⊙ f ⟺ f
  invu : ∀ {A B C} {f : A ⟷ B} {g : C ⟷ B}
    → f ⊙ dagger f ⊙ g ⊙ dagger g ⟺ g ⊙ dagger g ⊙ f ⊙ dagger f
  
-- ⊕ functorial
  fun⊕id : ∀ {A B} → id⟷ ⊕ id⟷ ⟺ id⟷ {A ⊕ B}
  fun⊕⊙ : ∀ {A B C D E F}
    → {f : A ⟷ B} {g : B ⟷ C} {h : D ⟷ E} {k : E ⟷ F}
    → (g ⊙ f) ⊕ (k ⊙ h) ⟺ (g ⊕ k) ⊙ (f ⊕ h)

-- ⊗ functorial
  fun⊗id : ∀ {A B} → id⟷ ⊗ id⟷ ⟺ id⟷ {A ⊗ B}
  fun⊗⊙ : ∀ {A B C D E F}
    → {f : A ⟷ B} {g : B ⟷ C} {h : D ⟷ E} {k : E ⟷ F}
    → (g ⊙ f) ⊗ (k ⊙ h) ⟺ (g ⊗ k) ⊙ (f ⊗ h)

-- λ⊕, α⊕ and s⊕ natural
  nλ⊕ : ∀ {A B} {f : A ⟷ B} → f ⊙ λ⊕ ⟺ λ⊕ ⊙ (id⟷ ⊕ f)
  nα⊕ : ∀ {A B C D E F} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → (f ⊕ (g ⊕ h)) ⊙ α⊕ ⟺ α⊕ ⊙ ((f ⊕ g) ⊕ h)
  ns⊕ : ∀ {A B C D} {f : A ⟷ B} {g : C ⟷ D} 
    → (f ⊕ g) ⊙ s⊕ ⟺ s⊕ ⊙ (g ⊕ f)

-- λ⊗, α⊗ and s⊗ natural
  nλ⊗ : ∀ {A B} {f : A ⟷ B} → f ⊙ λ⊗ ⟺ λ⊗ ⊙ (id⟷ ⊗ f)
  nα⊗ : ∀ {A B C D E F} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → (f ⊗ (g ⊗ h)) ⊙ α⊗ ⟺ α⊗ ⊙ ((f ⊗ g) ⊗ h)
  ns⊗ : ∀ {A B C D} {f : A ⟷ B} {g : C ⟷ D} 
    → (f ⊗ g) ⊙ s⊗ ⟺ s⊗ ⊙ (g ⊗ f)

-- κL and δR natural
  nκL : ∀ {A B} {f : A ⟷ B} → κL ⊙ (id⟷ ⊗ f) ⟺ κL
  nδR : ∀ {A B C D E F} {f : A ⟷ B} {g : C ⟷ D} {h : E ⟷ F}
    → ((f ⊗ h) ⊕ (g ⊗ h)) ⊙ δR ⟺ δR ⊙ ((f ⊕ g) ⊗ h)

-- ⊕ symmetric monoidal
  ραλ⊕ : ∀ {A B} →  ρ⊕-1 ⊕ id⟷ ⟺ (id⟷ ⊕ λ⊕) ⊙ α⊕ {A} {𝟘} {B}
  ααα⊕ : ∀ {A B C D}
    → α⊕ ⊙ α⊕ {A ⊕ B} {C} {D} ⟺ (id⟷ ⊕ α⊕) ⊙ α⊕ ⊙ (α⊕ ⊕ id⟷)
  ρsλ⊕ : ∀ {A} → ρ⊕-1 {A} ⟺ λ⊕ ⊙ s⊕
  ss⊕ : ∀ {A B} → s⊕ ⊙ s⊕ ⟺ id⟷ {A ⊕ B}
  sα⊕ : ∀ {A B C} 
    → α⊕ ⊙ s⊕ ⊙ α⊕ {A} {B} {C} ⟺ (id⟷ ⊕ s⊕) ⊙ α⊕ ⊙ (s⊕ ⊕ id⟷)

-- ⊗ symmetric monoidal
  ραλ⊗ : ∀ {A B} → ρ⊗-1 ⊗ id⟷ ⟺ (id⟷ ⊗ λ⊗) ⊙ α⊗ {A} {𝟙} {B}
  ααα⊗ : ∀ {A B C D}
    → α⊗ ⊙ α⊗ {A ⊗ B} {C} {D} ⟺ (id⟷ ⊗ α⊗) ⊙ α⊗ ⊙ (α⊗ ⊗ id⟷)
  ρsλ⊗ : ∀ {A} → ρ⊗-1 {A} ⟺ λ⊗ ⊙ s⊗
  ss⊗ : ∀ {A B} → s⊗ ⊙ s⊗ ⟺ id⟷ {A ⊗ B}
  sα⊗ : ∀ {A B C}
    → α⊗ ⊙ s⊗ ⊙ α⊗ {A} {B} {C} ⟺ (id⟷ ⊗ s⊗) ⊙ α⊗ ⊙ (s⊗ ⊗ id⟷)

-- Laplaza's coherence equations for rig categories
  I : ∀ {A B C} → s⊕ ⊙ δL {A} {B} {C} ⟺ δL ⊙ (id⟷ ⊗ s⊕)
  II : ∀ {A B C} → (s⊗ ⊕ s⊗) ⊙ δR {A} {B} {C} ⟺ δL ⊙ s⊗
  III :  ∀ {A B C} → s⊕ ⊙ δR {A} {B} {C} ⟺ δR ⊙ (s⊕ ⊗ id⟷)
  IV : ∀ {A B C D}
    → α⊕-1 ⊙ (id⟷ ⊕ δR) ⊙ δR {A} {B ⊕ C} {D} ⟺ (δR ⊕ id⟷) ⊙ δR ⊙ (α⊕-1 ⊗ id⟷)
  V : ∀ {A B C D}
    → α⊕-1 ⊙ (id⟷ ⊕ δL) ⊙ δL {A} {B} {C ⊕ D} ⟺ (δL ⊕ id⟷) ⊙ δL ⊙ (id⟷ ⊗ α⊕-1)
  VI : ∀ {A B C D}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δL ⊙ (id⟷ ⊗ δL) ⟺ δL ⊙ α⊗-1 {A} {B} {C ⊕ D}
  VII : ∀ {A B C D}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δR {A} {B} {C ⊗ D} ⟺ δR ⊙ (δR ⊗ id⟷) ⊙ α⊗-1
  VIII : ∀ {A B C D}
    → (α⊗-1 ⊕ α⊗-1) ⊙ δL ⊙ (id⟷ ⊗ δR) ⟺ δR ⊙ (δL ⊗ id⟷) ⊙ α⊗-1 {A} {B ⊕ C} {D}
  IX : ∀ {A B C D}
    → (α⊕-1 ⊕ id⟷) ⊙ ((id⟷ ⊕ s⊕) ⊕ id⟷) ⊙ (α⊕ ⊕ id⟷) ⊙ α⊕-1 ⊙ (δL ⊕ δL) ⊙ δR ⟺
      α⊕-1 ⊙ (δR ⊕ δR) ⊙ δL {A ⊕ B} {C} {D}
  X : κL {𝟘} ⟺ κR
  XI : ∀ {A B} → κL {A ⊕ B} ⟺ λ⊕ ⊙ (κL ⊕ κL) ⊙ δL
  XII : ∀ {A B} → κR {A ⊕ B} ⟺ λ⊕ ⊙ (κR ⊕ κR) ⊙ δR
  XIII : ρ⊗-1 {𝟘} ⟺ κL
  XIV : λ⊗ {𝟘} ⟺ κR
  XV : ∀ {A} → κR {A} ⟺ κL ⊙ s⊗
  XVI : ∀ {A B} → κL {A ⊗ B} ⟺ κL ⊙ (κL ⊗ id⟷) ⊙ α⊗-1
  XVII : ∀ {A B} → κR ⊙ (id⟷ ⊗ κL) ⟺ κL ⊙ (κR ⊗ id⟷) ⊙ α⊗-1 {A} {𝟘} {B}
  XVIII : ∀ {A B} → κR ⊙ α⊗-1 {A} {B} {𝟘} ⟺ κR ⊙ (id⟷ ⊗ κR)
  XIX : ∀ {A B} → id⟷ ⊗ λ⊕ ⟺ λ⊕ ⊙ (κR ⊕ id⟷) ⊙ δL {A} {𝟘} {B}
  XX : ∀  {A B} → λ⊕ ⊙ (κL ⊕ id⟷) ⊙ δR {𝟘} {A} {B} ⟺ λ⊕ ⊗ id⟷
  XXI : ∀  {A B} → ρ⊕-1 ⊙ (id⟷ ⊕ κR) ⊙ δL {A} {B} {𝟘} ⟺ id⟷ ⊗ ρ⊕-1
  XXII : ∀  {A B} → ρ⊕-1 ⊙ (id⟷ ⊕ κL) ⊙ δR {A} {𝟘} {B} ⟺ ρ⊕-1 ⊗ id⟷
  XXIII : ∀  {A B} → λ⊗ {A ⊕ B} ⟺ (λ⊗ ⊕ λ⊗) ⊙ δL
  XXIV : ∀  {A B} → ρ⊗-1 {A ⊕ B} ⟺ (ρ⊗-1 ⊕ ρ⊗-1) ⊙ δR

-- Trace axioms
  naturalityL : ∀ {A B C D} {f : C ⟷ D} {g : A ⊕ B ⟷ A ⊕ C}
    → f ⊙ trace g ⟺ trace ((id⟷ ⊕ f) ⊙ g)
  naturalityR : ∀ {A B C D} {f : B ⟷ C} {g : A ⊕ C ⟷ A ⊕ D}
    → trace g ⊙ f ⟺ trace (g ⊙ (id⟷ ⊕ f))
  dinaturality : ∀ {A B C D} {f : B ⟷ A} {g : A ⊕ C ⟷ B ⊕ D}
    → trace ((f ⊕ id⟷) ⊙ g) ⟺ trace (g ⊙ (f ⊕ id⟷))
  vanishingI : ∀ {A B} {f : 𝟘 ⊕ A ⟷ 𝟘 ⊕ B} → f ⟺ λ⊕-1 ⊙ trace f ⊙ λ⊕ 
  vanishingII : ∀ {A B C D} {f : (A ⊕ B) ⊕ C ⟷ (A ⊕ B) ⊕ D}
    → trace f ⟺ trace (trace (α⊕ ⊙ f ⊙ α⊕-1))
  yanking : ∀ {A} → trace s⊕ ⟺ id⟷ {A}
