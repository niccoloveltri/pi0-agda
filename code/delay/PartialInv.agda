{-# OPTIONS --without-K #-}

module delay.PartialInv where

open import Data.Product
open import Data.Sum
open import Function 
open import Relation.Binary.PropositionalEquality

open import Utilities
open import delay.Delay
open import delay.Monad
open import delay.Elgot

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

≅-to-≃₁ : ∀ {A B} → A ≅ B → A ≃₁ B
≅-to-≃₁ (f , tinv g α β) = now ∘ f ,
  (pinv (now ∘ g)
        (λ { _ _ now → subst (λ x → now (f (g _)) ↓ x) (α _) now })
        (λ { _ _ now → subst (λ x → now (g (f _)) ↓ x) (β _) now }))

_⊙≃₁_ : ∀ {A B C} → B ≃₁ C → A ≃₁ B → A ≃₁ C
(g , pinv g† i1 i2) ⊙≃₁ (f , pinv f† j1 j2) = (g ∙ f) , pinv (f† ∙ g†) α β
  where
    α : ∀ a c → bindD f† (g† c) ↓ a → bindD g (f a) ↓ c
    α a c p with bindD↓ f† (g† c) p
    ... | b , q , r = trans≈ (bindD-input↓ g (j1 a b r)) (i1 b c q) 

    β : ∀ c a → bindD g (f a) ↓ c → bindD f† (g† c) ↓ a
    β c a p with bindD↓ g (f a) p
    ... | b , q , r = trans≈ (bindD-input↓ f† (i2 c b r)) (j2 b a q)

_⊕≃₁_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A ⊎ B) ≃₁ (C ⊎ D)
_⊕≃₁_ {A}{B}{C}{D} (f , pinv f† i1 i2)  (g , pinv g† j1 j2) = h , pinv h† α β
  where
    h : A ⊎ B → Delay (C ⊎ D)
    h = [ mapD inj₁ ∘  f , mapD inj₂ ∘ g ]′

    h† : C ⊎ D → Delay (A ⊎ B)
    h† = [ mapD inj₁ ∘  f† , mapD inj₂ ∘ g† ]′

    α : ∀ x y → h† y ↓ x → h x ↓ y
    α (inj₁ a) (inj₁ c) p with bindD↓ (λ x → now (inj₁ x)) (f† c) p
    α (inj₁ a) (inj₁ c) p | .a , q , now = bindD-input↓ (λ x → now (inj₁ x)) (i1 a c q)
    α (inj₁ a) (inj₂ d) p with bindD↓ (λ x → now (inj₂ x)) (g† d) p
    α (inj₁ a) (inj₂ d) p | x , q , ()
    α (inj₂ b) (inj₁ c) p with bindD↓ (λ x → now (inj₁ x)) (f† c) p
    α (inj₂ b) (inj₁ c) p | x , q , ()
    α (inj₂ b) (inj₂ d) p with bindD↓ (λ x → now (inj₂ x)) (g† d) p
    α (inj₂ b) (inj₂ d) p | .b , q , now = bindD-input↓ (λ x → now (inj₂ x)) (j1 b d q)

    β : ∀ y x → h x ↓ y → h† y ↓ x
    β (inj₁ c) (inj₁ a) p with bindD↓ (λ x → now (inj₁ x)) (f a) p
    β (inj₁ c) (inj₁ a) p | .c , q , now = bindD-input↓ (λ x → now (inj₁ x)) (i2 c a q)
    β (inj₂ d) (inj₁ a) p with bindD↓ (λ x → now (inj₁ x)) (f a) p
    β (inj₂ d) (inj₁ a) p | x , q , ()
    β (inj₁ c) (inj₂ b) p with bindD↓ (λ x → now (inj₂ x)) (g b) p
    β (inj₁ c) (inj₂ b) p | x , q , ()
    β (inj₂ d) (inj₂ b) p with bindD↓ (λ x → now (inj₂ x)) (g b) p
    β (inj₂ d) (inj₂ b) p | .d , q , now = bindD-input↓ (λ x → now (inj₂ x)) (j2 d b q)

_⊗≃₁_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A × B) ≃₁ (C × D)
_⊗≃₁_ {A}{B}{C}{D} (f , pinv f† i1 i2) (g , pinv g† j1 j2) = h , (pinv h† α β)
  where
    h : A × B → Delay (C × D)
    h (a , b) = bindD (λ c → bindD (λ d → now (c , d)) (g b)) (f a)

    h† : C × D → Delay (A × B)
    h† (c , d) = bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d)

    α : ∀ x y → h† y ↓ x → h x ↓ y
    α (a , b) (c , d) p with bindD↓ (λ x → bindD (λ y → now (y , x)) (f† c)) (g† d) p
    ... | b' , q , r with bindD↓ (λ y → now (y , b')) (f† c) r
    α (a , b) (c , d) p | .b , q , r | .a , q' , now =
      trans≈ (bindD-input↓ (λ x → bindD (λ y → now (x , y)) (g b)) (i1 a c q'))
             (bindD-input↓ (λ y → now (c , y)) (j1 b d q))

    β : ∀ y x → h x ↓ y → h† y ↓ x
    β (c , d) (a , b) p with bindD↓ (λ x → bindD (λ y → now (x , y)) (g b)) (f a) p
    ... | c' , q , r with bindD↓ (λ y → now (c' , y)) (g b) r
    β (c , d) (a , b) p | .c , q , r | .d , q' , now =
      trans≈ (bindD-input↓ (λ y → bindD (λ x → now (x , y)) (f† c)) (j2 d b q'))
             (bindD-input↓ (λ x → now (x , b)) (i2 c a q))

trace≃₁ : ∀ {A B U} → (U ⊎ A) ≃₁ (U ⊎ B) → A ≃₁ B
trace≃₁ (f , pinv f† i1 i2) = traceD f , pinv (traceD f†) α β
  where
    α : ∀ a b → traceD f† b ↓ a → traceD f a ↓ b 
    α a b p = traceD-now-equiv₂ f (reverse-trace-reach f† f i1 (traceD-now-equiv₁ f† p))

    β : ∀ b a → traceD f a ↓ b → traceD f† b ↓ a 
    β b a p = traceD-now-equiv₂ f† (reverse-trace-reach f f† i2 (traceD-now-equiv₁ f p))

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
