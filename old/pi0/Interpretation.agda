{-# OPTIONS --without-K #-}

module pi0.Interpretation where

open import Data.Empty
open import Data.Sum renaming (map to map⊎; swap to swap⊎)
open import Data.Unit
open import Data.Product renaming (map to map×; swap to swap×)
open import Relation.Binary.PropositionalEquality hiding (naturality)
open import Function

open import pi0.Syntax
open import delay.Delay
open import delay.Monad
open import delay.Elgot
open import delay.PartialInv
open import delay.Structure

data SemCode : Set₁ where
  ℂ : Set → SemCode
  𝕀 : SemCode
  _⊕_ _⊗_ : SemCode → SemCode → SemCode

sem-decode : SemCode → Set → Set
sem-decode (ℂ A) _ = A
sem-decode 𝕀 A = A
sem-decode (ρ₁ ⊕ ρ₂) A = sem-decode ρ₁ A ⊎ sem-decode ρ₂ A
sem-decode (ρ₁ ⊗ ρ₂) A = sem-decode ρ₁ A × sem-decode ρ₂ A

data Mu (ρ : SemCode) : Set where
  sup : sem-decode ρ (Mu ρ) → Mu ρ

-- Interpretation of Π₀-types into Set

mutual
  ⟦_⟧U : U → Set
  ⟦ 𝟘 ⟧U = ⊥
  ⟦ 𝟙 ⟧U = ⊤
  ⟦ τ₁ ⊕ τ₂ ⟧U = ⟦ τ₁ ⟧U ⊎ ⟦ τ₂ ⟧U
  ⟦ τ₁ ⊗ τ₂ ⟧U = ⟦ τ₁ ⟧U × ⟦ τ₂ ⟧U
  ⟦ μ ρ ⟧U = Mu ⟦ ρ ⟧code

  ⟦_⟧code : Code → SemCode
  ⟦ ℂ τ ⟧code = ℂ ⟦ τ ⟧U
  ⟦ 𝕀 ⟧code = 𝕀
  ⟦ ρ₁ ⊕ ρ₂ ⟧code = ⟦ ρ₁ ⟧code ⊕ ⟦ ρ₂ ⟧code
  ⟦ ρ₁ ⊗ ρ₂ ⟧code = ⟦ ρ₁ ⟧code ⊗ ⟦ ρ₂ ⟧code

-- Interpretation of Π₀-programs into the Kleisli category of Delay

record is-total-inv {A B : Set} (f : A → B) : Set where
  constructor tinv
  field
    g : B → A
    α : ∀ x → f (g x) ≡ x
    β : ∀ x → g (f x) ≡ x

_≅_ : Set → Set → Set
A ≅ B = Σ (A → B) is-total-inv



total-to-partial-inv : ∀ {A B} → A ≅ B → A ≃₁ B
total-to-partial-inv (f , tinv g α β) = now ∘ f ,
  (pinv (now ∘ g)
        (λ { _ _ now → subst (λ x → now (f (g _)) ↓ x) (α _) now })
        (λ { _ _ now → subst (λ x → now (g (f _)) ↓ x) (β _) now }))

sem-id⟷ : ∀ {A} → A ≅ A
sem-id⟷ = id , tinv id (λ _ → refl) (λ _ → refl)

sem-λ⊕-f : {A : Set} → ⊥ ⊎ A → A
sem-λ⊕-f (inj₂ y) = y

sem-λ⊕ : ∀ {A} → (⊥ ⊎ A) ≅ A
sem-λ⊕ {A} = sem-λ⊕-f , tinv inj₂ (λ _ → refl) β
  where
    β : (x : ⊥ ⊎ A) → inj₂ (sem-λ⊕-f x) ≡ x
    β (inj₁ ())
    β (inj₂ x) = refl

sem-s⊕ : ∀ {A B} → (A ⊎ B) ≅ (B ⊎ A)
sem-s⊕ = swap⊎ , tinv swap⊎ α α
  where
    α : ∀ {X Y} (x : X ⊎ Y) → swap⊎ (swap⊎ x) ≡ x
    α (inj₁ x) = refl
    α (inj₂ y) = refl


sem-α⊕-f : {A B C : Set} → (A ⊎ (B ⊎ C)) → ((A ⊎ B) ⊎ C)
sem-α⊕-f (inj₁ x) = inj₁ (inj₁ x)
sem-α⊕-f (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
sem-α⊕-f (inj₂ (inj₂ y)) = inj₂ y

sem-α⊕-g : {A B C : Set} → ((A ⊎ B) ⊎ C) → (A ⊎ (B ⊎ C))
sem-α⊕-g (inj₁ (inj₁ x)) = inj₁ x
sem-α⊕-g (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
sem-α⊕-g (inj₂ y) = inj₂ (inj₂ y)

sem-α⊕ : ∀ {A B C} → (A ⊎ (B ⊎ C)) ≅ ((A ⊎ B) ⊎ C)
sem-α⊕ {A}{B}{C} = sem-α⊕-f , tinv sem-α⊕-g α β
  where
    α : ∀ x → sem-α⊕-f (sem-α⊕-g x) ≡ x
    α (inj₁ (inj₁ x)) = refl
    α (inj₁ (inj₂ y)) = refl
    α (inj₂ y) = refl

    β : ∀ x → sem-α⊕-g (sem-α⊕-f x) ≡ x
    β (inj₁ x) = refl
    β (inj₂ (inj₁ x)) = refl
    β (inj₂ (inj₂ y)) = refl

sem-λ⊗ : ∀ {A} → (⊤ × A) ≅ A
sem-λ⊗ {A} = proj₂ , tinv g (λ _ → refl) β
  where
    g : A → ⊤ × A
    g a = tt , a

    β : ∀ x → g (proj₂ x) ≡ x
    β (tt , a) = refl

sem-s⊗ : ∀ {A B} → (A × B) ≅ (B × A)
sem-s⊗ = swap× , tinv swap× (λ _ → refl) (λ _ → refl)

sem-α⊗ : ∀ {A B C} → (A × (B × C)) ≅ ((A × B) × C)
sem-α⊗ {A}{B}{C} = f , tinv g (λ _ → refl) (λ _ → refl)
  where
    f : A × B × C → (A × B) × C
    f (a , b , c) = (a , b) , c

    g : (A × B) × C → A × B × C
    g ((a , b) , c) = a , b , c


sem-κ : ∀ {A} → (⊥ × A) ≅ ⊥
sem-κ {A} = proj₁ , tinv ⊥-elim (λ ()) (λ { (() , _)})

sem-δ : ∀ {A B C} → ((A ⊎ B) × C) ≅ (A × C ⊎ B × C)
sem-δ {A}{B}{C} = f , tinv g α β
  where
    f : (A ⊎ B) × C → A × C ⊎ B × C
    f (inj₁ a , c) = inj₁ (a , c)
    f (inj₂ b , c) = inj₂ (b , c)

    g : A × C ⊎ B × C → (A ⊎ B) × C
    g (inj₁ (a , c)) = inj₁ a , c
    g (inj₂ (b , c)) = inj₂ b , c

    α : ∀ x → f (g x) ≡ x
    α (inj₁ (a , c)) = refl
    α (inj₂ (b , c)) = refl

    β : ∀ x → g (f x) ≡ x
    β (inj₁ a , c) = refl
    β (inj₂ b , c) = refl

_sem-⊙_ : ∀ {A B C} → B ≃₁ C → A ≃₁ B → A ≃₁ C
(g , pinv g† i1 i2) sem-⊙ (f , pinv f† j1 j2) = (g ∙ f) , pinv (f† ∙ g†) α β
  where
    α : ∀ a c → bindD f† (g† c) ↓ a → bindD g (f a) ↓ c
    α a c p with bindD↓ f† (g† c) p
    ... | b , q , r = trans≈ (bindD-input↓ g (j1 a b r)) (i1 b c q) 

    β : ∀ c a → bindD g (f a) ↓ c → bindD f† (g† c) ↓ a
    β c a p with bindD↓ g (f a) p
    ... | b , q , r = trans≈ (bindD-input↓ f† (i2 c b r)) (j2 b a q)

_sem-⊕_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A ⊎ B) ≃₁ (C ⊎ D)
_sem-⊕_ {A}{B}{C}{D} (f , pinv f† i1 i2)  (g , pinv g† j1 j2) = h , pinv h† α β
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

_sem-⊗_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A × B) ≃₁ (C × D)
_sem-⊗_ {A}{B}{C}{D} (f , pinv f† i1 i2) (g , pinv g† j1 j2) = h , (pinv h† α β)
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

_sem-⊗'_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A × B) ≃₁ (C × D)
_sem-⊗'_ {A}{B}{C}{D} (f , pinv f† i1 i2) (g , pinv g† j1 j2) = (f ×D g) , pinv (f† ×D g†) α β
  where
    α : ∀ x y → (f† ×D g†) y ↓ x → (f ×D g) x ↓ y
    α (a , b) (c , d) p with bindD↓ costr (bindD (λ x → now (f† c , x)) (g† d)) p
    ... | (z , b') , q , q' with bindD↓ (λ x → now (x , b')) z q'
    α (a , b) (c , d) p | (z , .b) , q , q' | .a , r , now with bindD↓ (λ x → now (f† c , x)) (g† d) q
    α (a , b) (c , d) p | (.(f† c) , .b) , q , q' | .a , r , now | .b , s , now =
      trans≈ (cong-bindD (cong-bindD (j1 _ _ s))) (cong-bindD (i1 _ _ r))

    β : ∀ x y → (f ×D g) y ↓ x → (f† ×D g†) x ↓ y
    β (c , d) (a , b) p = {!!}


sem-fold-f : ∀ ρ ρ' → ⟦ decode ρ' (μ ρ) ⟧U → sem-decode ⟦ ρ' ⟧code (Mu ⟦ ρ ⟧code)
sem-fold-f ρ (ℂ τ) = id
sem-fold-f ρ 𝕀 = id
sem-fold-f ρ (ρ₁ ⊕ ρ₂) = map⊎ (sem-fold-f ρ ρ₁) (sem-fold-f ρ ρ₂)
sem-fold-f ρ (ρ₁ ⊗ ρ₂) = map× (sem-fold-f ρ ρ₁) (sem-fold-f ρ ρ₂)

sem-fold-g : ∀ ρ ρ' → sem-decode ⟦ ρ' ⟧code (Mu ⟦ ρ ⟧code) → ⟦ decode ρ' (μ ρ) ⟧U
sem-fold-g ρ (ℂ τ) = id
sem-fold-g ρ 𝕀 = id
sem-fold-g ρ (ρ₁ ⊕ ρ₂) = map⊎ (sem-fold-g ρ ρ₁) (sem-fold-g ρ ρ₂)
sem-fold-g ρ (ρ₁ ⊗ ρ₂) = map× (sem-fold-g ρ ρ₁) (sem-fold-g ρ ρ₂)

sem-fold-α : ∀ ρ ρ' x → sem-fold-f ρ ρ' (sem-fold-g ρ ρ' x) ≡ x
sem-fold-α ρ (ℂ τ) x = refl
sem-fold-α ρ 𝕀 x = refl
sem-fold-α ρ (ρ' ⊕ ρ'') (inj₁ x) = cong inj₁ (sem-fold-α ρ ρ' x)
sem-fold-α ρ (ρ' ⊕ ρ'') (inj₂ y) = cong inj₂ (sem-fold-α ρ ρ'' y)
sem-fold-α ρ (ρ' ⊗ ρ'') (x , y) = cong₂ _,_ (sem-fold-α ρ ρ' x) (sem-fold-α ρ ρ'' y)

sem-fold-β : ∀ ρ ρ' x → sem-fold-g ρ ρ' (sem-fold-f ρ ρ' x) ≡ x
sem-fold-β ρ (ℂ τ) x = refl
sem-fold-β ρ 𝕀 x = refl
sem-fold-β ρ (ρ' ⊕ ρ'') (inj₁ x) = cong inj₁ (sem-fold-β ρ ρ' x)
sem-fold-β ρ (ρ' ⊕ ρ'') (inj₂ y) = cong inj₂ (sem-fold-β ρ ρ'' y)
sem-fold-β ρ (ρ' ⊗ ρ'') (x , y) = cong₂ _,_ (sem-fold-β ρ ρ' x) (sem-fold-β ρ ρ'' y)


sem-fold : ∀ ρ → ⟦ decode ρ (μ ρ) ⟧U ≅ Mu ⟦ ρ ⟧code
sem-fold ρ = f , tinv g α β
  where
    f : ⟦ decode ρ (μ ρ) ⟧U → Mu ⟦ ρ ⟧code
    f = sup ∘ sem-fold-f ρ ρ

    g : Mu ⟦ ρ ⟧code → ⟦ decode ρ (μ ρ) ⟧U
    g (sup x) = sem-fold-g ρ ρ x

    α : ∀ x → f (g x) ≡ x
    α (sup x) = cong sup (sem-fold-α ρ ρ x)

    β : ∀ x → g (f x) ≡ x
    β = sem-fold-β ρ ρ

sem-trace : ∀ {A B U} → (U ⊎ A) ≃₁ (U ⊎ B) → A ≃₁ B
sem-trace (f , pinv f† i1 i2) = traceD f , pinv (traceD f†) α β
  where
    α : ∀ a b → traceD f† b ↓ a → traceD f a ↓ b 
    α a b p = traceD-now-equiv₂ f (reverse-trace-reach f† f i1 (traceD-now-equiv₁ f† p))

    β : ∀ b a → traceD f a ↓ b → traceD f† b ↓ a 
    β b a p = traceD-now-equiv₂ f† (reverse-trace-reach f f† i2 (traceD-now-equiv₁ f p))

⟦_⟧⟷ : ∀ {A B} → A ⟷ B → ⟦ A ⟧U ≃₁ ⟦ B ⟧U
⟦ id⟷ ⟧⟷ = total-to-partial-inv sem-id⟷
⟦ λ⊕ ⟧⟷ = total-to-partial-inv sem-λ⊕
⟦ λ⊕-1 ⟧⟷ = sem-dagger (total-to-partial-inv sem-λ⊕)
⟦ s⊕ ⟧⟷ = total-to-partial-inv sem-s⊕ 
⟦ α⊕-1 ⟧⟷ = total-to-partial-inv sem-α⊕
⟦ α⊕ ⟧⟷ = sem-dagger (total-to-partial-inv sem-α⊕)
⟦ λ⊗ ⟧⟷ = total-to-partial-inv sem-λ⊗
⟦ λ⊗-1 ⟧⟷ = sem-dagger (total-to-partial-inv sem-λ⊗)
⟦ s⊗ ⟧⟷ = total-to-partial-inv sem-s⊗
⟦ α⊗-1 ⟧⟷ = total-to-partial-inv sem-α⊗ 
⟦ α⊗ ⟧⟷ = sem-dagger (total-to-partial-inv sem-α⊗)
⟦ κL ⟧⟷ = total-to-partial-inv sem-κ 
⟦ κL-1 ⟧⟷ = sem-dagger (total-to-partial-inv sem-κ) 
⟦ δR ⟧⟷ = total-to-partial-inv sem-δ 
⟦ δR-1 ⟧⟷ = sem-dagger (total-to-partial-inv sem-δ)
⟦ f ⊙ g ⟧⟷ = ⟦ f ⟧⟷ sem-⊙ ⟦ g ⟧⟷
⟦ f ⊕ g ⟧⟷ = ⟦ f ⟧⟷ sem-⊕ ⟦ g ⟧⟷
⟦ f ⊗ g ⟧⟷ = ⟦ f ⟧⟷ sem-⊗' ⟦ g ⟧⟷
⟦ fold ρ ⟧⟷ = total-to-partial-inv (sem-fold ρ)
⟦ unfold ρ ⟧⟷ = sem-dagger (total-to-partial-inv (sem-fold ρ))
⟦ trace p ⟧⟷ = sem-trace ⟦ p ⟧⟷

-- Interpretation of Π₀-program equivalences into the Kleisli category of Delay

sem-⊕₂ : ∀ {A B C D} {f g : A ≃₁ B} {f' g' : C ≃₁ D}
  → f ≃₂ g → f' ≃₂ g'
  → (f sem-⊕ f') ≃₂ (g sem-⊕ g')
sem-⊕₂ p q (inj₁ x) = cong-bindD (p x)
sem-⊕₂ p q (inj₂ y) = cong-bindD (q y)

-- Trace axioms

naturalityL-traceD : ∀ {A B C D} {f : C → Delay D} {g : A ⊎ B → Delay (A ⊎ C)}
                   → f ∙ traceD g ∼ traceD ([ (λ x → now (inj₁ x)) , mapD inj₂ ∘ f ]′ ∙ g)
naturalityL-traceD {f = f}{g} x =
  trans≈ (M3 ((g R) x))
    (trans≈ (cong-app-bindD ((g R) x) (λ { (inj₁ a) → naturality f (g L) a
                                         ; (inj₂ c) → trans≈ (sym≈ (M2 (f c))) (sym≈ (M3 (f c))) }))
            (sym≈ (M3 ((g R) x))))

naturalityR-traceD : ∀ {A B C D} {f : D → Delay B} {g : A ⊎ B → Delay (A ⊎ C)}
                   → traceD g ∙ f ∼ traceD (g ∙ [ (λ x → now (inj₁ x)) , mapD inj₂ ∘ f ]′)
naturalityR-traceD {f = f} x = trans≈ (sym≈ (M3 (f x))) (cong-bindD (sym≈ (M3 (f x))))

vanishingI-traceD : ∀ {A B} {f : ⊥ ⊎ A → Delay (⊥ ⊎ B)}
  → f ∼ ((λ x → now (inj₂ x)) ∙ traceD f) ∙ (now ∘ sem-λ⊕-f)
vanishingI-traceD {f = f} (inj₂ y) =
  trans≈ (sym≈ (M2 ((f R) y)))
    (trans≈ (cong-app-bindD ((f R) y) (λ { (inj₂ x) → refl≈ }))
      (sym≈ (M3 ((f R) y))))

mutual
  bekic↓₁₁' : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → bindD [ iterD ([ (iterD (mapD sem-α⊕-g ∘ f)) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) , now ]′ (iterD' (mapD sem-α⊕-g ∘ f)  (mapD sem-α⊕-g x)) ↓ c
  bekic↓₁₁' f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₁₁' f g (f x) p)
  bekic↓₁₁' f g (now (inj₁ (inj₂ y))) (laterL p) = bekic↓₁₂ f g (g y) p
  bekic↓₁₁' f g (now (inj₂ y)) p = p
  bekic↓₁₁' f g (later x) (laterL p) = laterL (bekic↓₁₁' f g (force x) p)

  bekic↓₁₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → iterD' ([ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) (iterD' ((λ {x} → mapD sem-α⊕-g) ∘ f) (mapD sem-α⊕-g x)) ↓ c
  bekic↓₁₁ f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₁₁ f g (f x) p)
  bekic↓₁₁ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₁₂ f g (g y) p)
  bekic↓₁₁ f g (now (inj₂ y)) p = p
  bekic↓₁₁ f g (later x) (laterL p) = laterL (bekic↓₁₁ f g (force x) p)
  
  bekic↓₁₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → iterD' ([ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) (bindD [ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ (mapD sem-α⊕-g x)) ↓ c
  bekic↓₁₂ f g (now (inj₁ (inj₁ x))) (laterL p) = bekic↓₁₁ f g (f x) p
  bekic↓₁₂ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₁₂ f g (g y) p)
  bekic↓₁₂ f g (now (inj₂ y)) p = p
  bekic↓₁₂ f g (later x) (laterL p) = laterL (bekic↓₁₂ f g (force x) p)

bekic↓₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : A ⊎ B) {c : C}
  → iterD [ f , g ]′ x ↓ c
  → bindD [ iterD ([ (iterD (mapD sem-α⊕-g ∘ f)) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) , now ]′ ([ iterD (mapD sem-α⊕-g ∘ f) , (λ z → now (inj₁ z)) ]′ x) ↓ c
bekic↓₁ f g (inj₁ x) p = bekic↓₁₁' f g (f x) p
bekic↓₁ f g (inj₂ y) p = bekic↓₁₂ f g (g y) p  

mutual
  bekic↓₂₁' : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → bindD [ iterD ([ (iterD (mapD sem-α⊕-g ∘ f)) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) , now ]′ (iterD' (mapD sem-α⊕-g ∘ f)  (mapD sem-α⊕-g x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₁' f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₂₁' f g (f x) p)
  bekic↓₂₁' f g (now (inj₁ (inj₂ y))) p = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₁' f g (now (inj₂ y)) p = p
  bekic↓₂₁' f g (later x) (laterL p) = laterL (bekic↓₂₁' f g (force x) p)

  bekic↓₂₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' ([ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) (iterD' ((λ {x} → mapD sem-α⊕-g) ∘ f) (mapD sem-α⊕-g x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₁ f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₂₁ f g (f x) p)
  bekic↓₂₁ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₁ f g (now (inj₂ y)) p = p
  bekic↓₂₁ f g (later x) (laterL p) = laterL (bekic↓₂₁ f g (force x) p)

  bekic↓₂₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' ([ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) (bindD [ iterD ((λ {x} → mapD sem-α⊕-g) ∘ f) , now ]′ (mapD sem-α⊕-g x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₂ f g (now (inj₁ (inj₁ x))) p = laterL (bekic↓₂₁ f g (f x) p) 
  bekic↓₂₂ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₂ f g (now (inj₂ y)) p = p
  bekic↓₂₂ f g (later x) (laterL p) = laterL (bekic↓₂₂ f g (force x) p)

bekic↓₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : A ⊎ B) {c : C}
  → bindD [ iterD ([ (iterD (mapD sem-α⊕-g ∘ f)) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) , now ]′ ([ iterD (mapD sem-α⊕-g ∘ f) , (λ z → now (inj₁ z)) ]′ x) ↓ c
  → iterD [ f , g ]′ x ↓ c
bekic↓₂ f g (inj₁ x) p = bekic↓₂₁' f g (f x) p
bekic↓₂ f g (inj₂ y) p = bekic↓₂₂ f g (g y) p

bekic : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C))
  → iterD [ f , g ]′ ∼
    [ iterD ([ (iterD (mapD sem-α⊕-g ∘ f)) , now ]′ ∙ (mapD sem-α⊕-g ∘ g)) , now ]′ ∙ [ iterD (mapD sem-α⊕-g ∘ f) , (λ z → now (inj₁ z)) ]′
bekic f g x = ≈-equiv₂ (bekic↓₁ f g x , bekic↓₂ f g x)  

copair∼ : {A B C : Set} {f f' : A → Delay C} {g g' : B → Delay C}
  → f ∼ f' → g ∼ g' → [ f , g ]′ ∼ [ f' , g' ]′
copair∼ p q (inj₁ x) = p x
copair∼ p q (inj₂ y) = q y  

vanishingII-traceD : ∀ {A B C D} {f : (A ⊎ B) ⊎ C → Delay ((A ⊎ B) ⊎ D)}
    → traceD f ∼ traceD (traceD (mapD sem-α⊕-g ∘ f ∘ sem-α⊕-f))
vanishingII-traceD {A}{B}{C}{D} {f = f} =
  proof
    traceD f
  ∼〈 refl∼ 〉
    [ iterD (f L) , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (copair∼ (cong-iterD (λ { (inj₁ x) → refl≈ ; (inj₂ y) → refl≈ })) refl∼) refl∼ 〉
    [ iterD [ f L L , f L R ]′ , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (copair∼ (bekic (f L L) (f L R)) refl∼) refl∼ 〉
    [ [ iterD ([ (iterD (mapD sem-α⊕-g ∘ (f L L))) , now ]′ ∙ (mapD sem-α⊕-g ∘ (f L R))) , now ]′ ∙ [ iterD (mapD sem-α⊕-g ∘ (f L L)) , (λ z → now (inj₁ z)) ]′ , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (λ { (inj₁ (inj₁ y)) → refl≈ ; (inj₁ (inj₂ y)) → refl≈ ; (inj₂ y) → refl≈ }) refl∼ 〉
    (([ iterD ([ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′ ∙ (mapD sem-α⊕-g ∘ (f L R))) , now ]′ ∙ [ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′) ∘ sem-α⊕-g) ∙ (f R)
  ∼〈 sym∼ (assoc∙ {f = f R}) 〉
    ([ iterD ([ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′ ∙ (mapD sem-α⊕-g ∘ (f L R))) , now ]′ ∙ [ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′) ∙ (mapD sem-α⊕-g ∘ (f R))
  ∼〈 sym∼ (assoc∙ {f = mapD sem-α⊕-g ∘ (f R)}) 〉
    [ iterD ([ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′ ∙ (mapD sem-α⊕-g ∘ (f L R))) , now ]′ ∙ ([ iterD (mapD sem-α⊕-g ∘ (f L L)) , now ]′ ∙ (mapD sem-α⊕-g ∘ (f R)))
  ∼〈 refl∼ 〉
    [ iterD ((traceD (mapD sem-α⊕-g ∘ f ∘ sem-α⊕-f)) L) , now ]′ ∙ ((traceD (mapD sem-α⊕-g ∘ f ∘ sem-α⊕-f)) R)
  ∼〈 refl∼ 〉
    traceD (traceD (mapD sem-α⊕-g ∘ f ∘ sem-α⊕-f))
  qed
  where
    open Eq∼

bind-mapD : ∀ {A B C} {f : A → B} {g : B → Delay C}
  → g ∙ mapD f ∼ bindD (g ∘ f)
bind-mapD = M3

dinaturality-traceD : ∀ {A B C D} {f : B → Delay A} {g : A ⊎ C → Delay (B ⊎ D)}
    → traceD ([ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ g) ∼ traceD (g ∙ [ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′) 
dinaturality-traceD {f = f}{g} =
  proof
    traceD ([ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ g)
  ∼〈 refl∼ 〉
    [ iterD ([ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ (g L)) , now ]′ ∙ ([ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ (g R))
  ∼〈 cong∙ {f = [ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ (g R)} (copair∼ (dinatural (g L) (mapD inj₁ ∘ f)) refl∼) refl∼ 〉
    [ [ iterD ([ g L , (λ z → now (inj₂ z)) ]′ ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g L) , now ]′ ∙ ([ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′ ∙ (g R))
  ∼〈 assoc∙ {f = g R} 〉
    ([ [ iterD ([ g L , (λ z → now (inj₂ z)) ]′ ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g L) , now ]′ ∙ [ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′) ∙ (g R)
  ∼〈 cong∙ {f = g R} (λ { (inj₁ x) → refl≈ ; (inj₂ y) → refl≈}) refl∼ 〉
    [ ([ [ iterD ([ g L , (λ z → now (inj₂ z)) ]′ ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g L) , now ]′ ∙ mapD inj₁) ∘ f , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (cong∙ {f = now ∘ f} (bind-mapD {f = inj₁}{[ [ iterD ([ g L , (λ z → now (inj₂ z)) ]′ ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g L) , now ]′}) refl∼) refl∼) refl∼ 〉
    [ ([ iterD ([ g L , (λ z → now (inj₂ z)) ]′ ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g L)) ∙ f , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (sym∼ (assoc∙ {f = f})) refl∼) refl∼ 〉
    [ [ iterD (([ g L , (λ z → now (inj₂ z)) ]′ ∙ mapD inj₁) ∘ f) , now ]′ ∙ ((g L) ∙ f) , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (cong∙ {f = (g L) ∙ f} (copair∼ (cong-iterD (cong∙ {f = now ∘ f} (bind-mapD {f = inj₁}{[ g L , (λ z → now (inj₂ z)) ]′}) refl∼)) refl∼) refl∼) refl∼) refl∼ 〉
    [ [ iterD ((g L) ∙ f) , now ]′ ∙ ((g L) ∙ f) , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (unfolding ((g L) ∙ f)) refl∼) refl∼ 〉
    [ iterD ((g L) ∙ f) , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (cong-iterD (sym∼ (M3 ∘ f))) refl∼) refl∼ 〉
    [ iterD (g ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g R)
  ∼〈 refl∼ 〉
    traceD (g ∙ [ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′)
  qed
  where
    open Eq∼

dagger-≃₂ : ∀ {A B} (f : A ⟷ B) → ⟦ dagger f ⟧⟷ ≃₂ sem-dagger ⟦ f ⟧⟷
dagger-≃₂ id⟷ = refl∼
dagger-≃₂ λ⊕ = refl∼
dagger-≃₂ λ⊕-1 = refl∼
dagger-≃₂ α⊕ = refl∼
dagger-≃₂ α⊕-1 = refl∼
dagger-≃₂ s⊕ = refl∼
dagger-≃₂ λ⊗ = refl∼
dagger-≃₂ λ⊗-1 = refl∼
dagger-≃₂ α⊗ = refl∼
dagger-≃₂ α⊗-1 = refl∼
dagger-≃₂ s⊗ = refl∼
dagger-≃₂ κL = refl∼
dagger-≃₂ κL-1 = refl∼
dagger-≃₂ δR = refl∼
dagger-≃₂ δR-1 = refl∼
dagger-≃₂ (f ⊙ f₁) = cong∙ (dagger-≃₂ f₁) (dagger-≃₂ f)
dagger-≃₂ (f ⊕ f₁) (inj₁ x) = cong-bindD (dagger-≃₂ f x)
dagger-≃₂ (f ⊕ f₁) (inj₂ y) = cong-bindD (dagger-≃₂ f₁ y)
dagger-≃₂ (f ⊗ f₁) (x , y) = cong-θ (dagger-≃₂ f x) (dagger-≃₂ f₁ y)
dagger-≃₂ (fold F) = refl∼
dagger-≃₂ (unfold F) = refl∼
dagger-≃₂ (trace f) x =
  cong-bindD₂ (copair∼ (cong-iterD (λ y → dagger-≃₂ f (inj₁ y))) refl∼)
              (dagger-≃₂ f (inj₂ x))

sem-linv : ∀ {A B} {f : A ≃₁ B} → (proj₁ f ∙ proj₁ (sem-dagger f)) ∙ proj₁ f ∼ proj₁ f
sem-linv {f = f , pinv f† p q} x = ≈-equiv₂
  ({!!} ,
   {!!})



⟦_⟧⟺ : ∀ {A B} {f g : A ⟷ B} → f ⟺ g → ⟦ f ⟧⟷ ≃₂ ⟦ g ⟧⟷
⟦ id⟺ ⟧⟺ = refl∼
⟦ trans⟺ e e₁ ⟧⟺ = trans∼ ⟦ e₁ ⟧⟺ ⟦ e ⟧⟺
⟦ e ⊙ e₁ ⟧⟺ = cong∙ ⟦ e ⟧⟺ ⟦ e₁ ⟧⟺
⟦_⟧⟺ (_⊕_ {f = f}{g}{f'}{g'} e e₁) =
  sem-⊕₂ {f = ⟦ f ⟧⟷}{⟦ g ⟧⟷}{⟦ f' ⟧⟷}{⟦ g' ⟧⟷} ⟦ e ⟧⟺ ⟦ e₁ ⟧⟺
⟦_⟧⟺ (_⊗_ {f = f} e e₁) (x , y) = {!!}
--  trans≈ (cong-app-bindD (proj₁ ⟦ f ⟧⟷ x) (λ z → cong-bindD (⟦ e₁ ⟧⟺ y)))
--         (cong-bindD (⟦ e ⟧⟺ x))
⟦ lid ⟧⟺ _ = M2 _
⟦ rid ⟧⟺ = refl∼
⟦ ass {f = f} ⟧⟺ x = M3 (proj₁ ⟦ f ⟧⟷ x)
⟦ inve {f = f} ⟧⟺ = trans∼ (cong∙ {f = proj₁ ⟦ f ⟧⟷} (cong∙ refl∼ (dagger-≃₂ f)) refl∼) (sem-linv {f = ⟦ f ⟧⟷})
⟦ invu ⟧⟺ = {!!}
⟦ fun⊕id ⟧⟺ = {!!}
⟦ fun⊕⊙ ⟧⟺ = {!!}
⟦ fun⊗id ⟧⟺ = refl∼
⟦ fun⊗⊙ ⟧⟺ = {!!}
⟦ nλ⊕ ⟧⟺ = {!!}
⟦ nα⊕ ⟧⟺ = {!!}
⟦ ns⊕ ⟧⟺ = {!!}
⟦ nλ⊗ ⟧⟺ = {!!}
⟦ nα⊗ ⟧⟺ = {!!}
⟦ ns⊗ ⟧⟺ = {!!}
⟦ nκL ⟧⟺ = {!!}
⟦ nδR ⟧⟺ = {!!}
⟦ ραλ⊕ ⟧⟺ = {!!}
⟦ ααα⊕ ⟧⟺ = {!!}
⟦ ρsλ⊕ ⟧⟺ = {!!}
⟦ ss⊕ ⟧⟺ = {!!}
⟦ sα⊕ ⟧⟺ = {!!}
⟦ ραλ⊗ ⟧⟺ = {!!}
⟦ ααα⊗ ⟧⟺ = {!!}
⟦ ρsλ⊗ ⟧⟺ = {!!}
⟦ ss⊗ ⟧⟺ = {!!}
⟦ sα⊗ ⟧⟺ = {!!}
⟦ I ⟧⟺ = {!!}
⟦ II ⟧⟺ = {!!}
⟦ III ⟧⟺ = {!!}
⟦ IV ⟧⟺ = {!!}
⟦ V ⟧⟺ = {!!}
⟦ VI ⟧⟺ = {!!}
⟦ VII ⟧⟺ = {!!}
⟦ VIII ⟧⟺ = {!!}
⟦ IX ⟧⟺ = {!!}
⟦ X ⟧⟺ = {!!}
⟦ XI ⟧⟺ = {!!}
⟦ XII ⟧⟺ = {!!}
⟦ XIII ⟧⟺ = {!!}
⟦ XIV ⟧⟺ = {!!}
⟦ XV ⟧⟺ = {!!}
⟦ XVI ⟧⟺ = {!!}
⟦ XVII ⟧⟺ = {!!}
⟦ XVIII ⟧⟺ = {!!}
⟦ XIX ⟧⟺ = {!!}
⟦ XX ⟧⟺ = {!!}
⟦ XXI ⟧⟺ = {!!}
⟦ XXII ⟧⟺ = {!!}
⟦ XXIII ⟧⟺ = {!!}
⟦ XXIV ⟧⟺ = {!!}
⟦ naturalityL {f = f}{g} ⟧⟺ = naturalityL-traceD {f = proj₁ ⟦ f ⟧⟷} {proj₁ ⟦ g ⟧⟷}
⟦ naturalityR {f = f} ⟧⟺ = naturalityR-traceD {f = proj₁ ⟦ f ⟧⟷}
⟦ dinaturality {f = f}{g} ⟧⟺ = dinaturality-traceD {f = proj₁ ⟦ f ⟧⟷} {proj₁ ⟦ g ⟧⟷} 
⟦ vanishingI {f = f} ⟧⟺ = vanishingI-traceD {f = proj₁ ⟦ f ⟧⟷}
⟦ vanishingII {f = f} ⟧⟺ = vanishingII-traceD {f = proj₁ ⟦ f ⟧⟷}
⟦ yanking ⟧⟺ = refl∼






{-
total-to-partial-inv : ∀ {A B} → A ≅ B → A ≃₁ B
total-to-partial-inv (f , tinv g α β) = now ∘ f ,
  (pinv (now ∘ g)
        (λ x → subst (λ z → now (f (g x)) ↓ z) (α x) now)
        (λ x → subst (λ z → now (g (f x)) ↓ z) (β x) now))

sem-id⟷ : ∀ {A} → A ≅ A
sem-id⟷ = id , tinv id (λ _ → refl) (λ _ → refl)

sem-unite⊕l : ∀ {A} → (⊥ ⊎ A) ≃₁ A
sem-unite⊕l {A} = f , pinv g (λ _ → now) β
  where
    f : ⊥ ⊎ A → Delay A
    f (inj₁ ())
    f (inj₂ x) = now x

    g : A → Delay (⊥ ⊎ A)
    g x = now (inj₂ x)

    β : g ∙ f ∼ ⌊ f ⌋
    β (inj₁ ())
    β (inj₂ x) = now

sem-swap⊕ : ∀ {A B} → (A ⊎ B) ≃₁ (B ⊎ A)
sem-swap⊕ = f , pinv f α α
  where
    f : ∀ {X Y} → X ⊎ Y → Delay (Y ⊎ X)
    f (inj₁ x) = now (inj₂ x)
    f (inj₂ y) = now (inj₁ y)

    α : ∀ {X Y} → f ∙ f ∼ ⌊ f {X}{Y} ⌋
    α (inj₁ x) = now
    α (inj₂ y) = now

sem-assocλ⊕ : ∀ {A B C} → (A ⊎ (B ⊎ C)) ≃₁ ((A ⊎ B) ⊎ C)
sem-assocλ⊕ {A}{B}{C} = f , pinv g α β
  where
    f : A ⊎ B ⊎ C → Delay ((A ⊎ B) ⊎ C)
    f (inj₁ x) = now (inj₁ (inj₁ x))
    f (inj₂ (inj₁ x)) = now (inj₁ (inj₂ x))
    f (inj₂ (inj₂ y)) = now (inj₂ y)

    g : (A ⊎ B) ⊎ C → Delay (A ⊎ B ⊎ C)
    g (inj₁ (inj₁ x)) = now (inj₁ x)
    g (inj₁ (inj₂ y)) = now (inj₂ (inj₁ y))
    g (inj₂ y) = now (inj₂ (inj₂ y))

    α : f ∙ g ∼ ⌊ g ⌋
    α (inj₁ (inj₁ x)) = now
    α (inj₁ (inj₂ y)) = now
    α (inj₂ y) = now

    β : g ∙ f ∼ ⌊ f ⌋
    β (inj₁ x) = now
    β (inj₂ (inj₁ x)) = now
    β (inj₂ (inj₂ y)) = now

sem-unite⊗l : ∀ {A} → (⊤ × A) ≃₁ A
sem-unite⊗l {A} = f , pinv g α β
  where
    f : ⊤ × A → Delay A
    f (tt , a) = now a

    g : A → Delay (⊤ × A)
    g a = now (tt , a)

    α : f ∙ g ∼ ⌊ g ⌋
    α a = now

    β : g ∙ f ∼ ⌊ f ⌋
    β (tt , a) = now
    
sem-swap⊗ : ∀ {A B} → (A × B) ≃₁ (B × A)
sem-swap⊗ = f , pinv f α α
  where
    f : ∀{A B} → A × B → Delay (B × A)
    f (a , b) = now (b , a)

    α : ∀ {A B} → f ∙ f ∼ ⌊ f {A}{B} ⌋
    α (a , b) = now

sem-assocλ⊗ : ∀ {A B C} → (A × (B × C)) ≃₁ ((A × B) × C)
sem-assocλ⊗ {A}{B}{C} = f , pinv g α β
  where
    f : A × B × C → Delay ((A × B) × C)
    f (a , b , c) = now ((a , b) , c)

    g : (A × B) × C → Delay (A × B × C)
    g ((a , b) , c) = now (a , b , c)

    α : f ∙ g ∼ ⌊ g ⌋
    α ((a , b) , c) = now

    β : g ∙ f ∼ ⌊ f ⌋
    β (a , b , c) = now

sem-absorbr : ∀ {A} → (⊥ × A) ≃₁ ⊥
sem-absorbr {A} = f , (pinv ⊥-elim α β)
  where
    f : ⊥ × A → Delay ⊥
    f (() , a)

    α : f ∙ ⊥-elim ∼ ⌊ ⊥-elim ⌋
    α ()

    β : ⊥-elim ∙ f ∼ ⌊ f ⌋
    β (() , a)

sem-dist : ∀ {A B C} → ((A ⊎ B) × C) ≃₁ (A × C ⊎ B × C)
sem-dist {A}{B}{C} = f , pinv g α β
  where
    f : (A ⊎ B) × C → Delay (A × C ⊎ B × C)
    f (inj₁ a , c) = now (inj₁ (a , c))
    f (inj₂ b , c) = now (inj₂ (b , c))

    g : A × C ⊎ B × C → Delay ((A ⊎ B) × C)
    g (inj₁ (a , c)) = now (inj₁ a , c)
    g (inj₂ (b , c)) = now (inj₂ b , c)

    α : f ∙ g ∼ ⌊ g ⌋
    α (inj₁ (a , c)) = now
    α (inj₂ (b , c)) = now

    β : g ∙ f ∼ ⌊ f ⌋
    β (inj₁ a , c) = now
    β (inj₂ b , c) = now

_sem-⊙_ : ∀ {A B C} → B ≃₁ C → A ≃₁ B → A ≃₁ C
(g , pinv g† i1 i2) sem-⊙ (f , pinv f† j1 j2) = (g ∙ f) , pinv (f† ∙ g†) α β
  where
    open Eq∼
    α : (g ∙ f) ∙ (f† ∙ g†) ∼ ⌊ f† ∙ g† ⌋
    α =
      proof
        (g ∙ f) ∙ (f† ∙ g†)
      ∼〈 sym∼ (assoc∙ {f = f† ∙ g†}) 〉
        g ∙ (f ∙ (f† ∙ g†))
      ∼〈 g ∙∼ assoc∙ {f = g†} 〉
        g ∙ ((f ∙ f†) ∙ g†)
      ∼〈 g ∙∼ (j1 ∼∙ g†) 〉
        g ∙ (⌊ f† ⌋ ∙ g†)
      ∼〈 g ∙∼ (R4 {f = g†}) 〉
        g ∙ (g† ∙ ⌊ f† ∙ g† ⌋)
      ∼〈 assoc∙ {f = ⌊ f† ∙ g† ⌋} 〉
        (g ∙ g†) ∙ ⌊ f† ∙ g† ⌋
      ∼〈 i1 ∼∙ ⌊ f† ∙ g† ⌋ 〉
        ⌊ g† ⌋ ∙ ⌊ f† ∙ g† ⌋
      ∼〈 R2 {f = g†}{f† ∙ g†} 〉
        ⌊ f† ∙ g† ⌋ ∙ ⌊ g† ⌋
      ∼〈 R3 {f = g†}{f† ∙ g†} 〉
        ⌊ (f† ∙ g†) ∙ ⌊ g† ⌋ ⌋ 
      ∼〈 cong-rest (sym∼ (assoc∙ {f = ⌊ g† ⌋})) 〉
        ⌊ f† ∙ (g† ∙ ⌊ g† ⌋) ⌋ 
      ∼〈 cong-rest (f† ∙∼ (R1 {f = g†})) 〉
        ⌊ f† ∙ g† ⌋
      qed

    β : (f† ∙ g†) ∙ (g ∙ f) ∼ ⌊ g ∙ f ⌋
    β =
      proof
        (f† ∙ g†) ∙ (g ∙ f)
      ∼〈 sym∼ (assoc∙ {f = g ∙ f}) 〉
        f† ∙ (g† ∙ (g ∙ f))
      ∼〈 f† ∙∼ assoc∙ {f = f} 〉
        f† ∙ ((g† ∙ g) ∙ f)
      ∼〈 f† ∙∼ (i2 ∼∙ f) 〉
        f† ∙ (⌊ g ⌋ ∙ f)
      ∼〈 f† ∙∼ (R4 {f = f}) 〉
        f† ∙ (f ∙ ⌊ g ∙ f ⌋)
      ∼〈 assoc∙ {f = ⌊ g ∙ f ⌋} 〉
        (f† ∙ f) ∙ ⌊ g ∙ f ⌋
      ∼〈 j2 ∼∙ ⌊ g ∙ f ⌋ 〉
        ⌊ f ⌋ ∙ ⌊ g ∙ f ⌋
      ∼〈 R2 {f = f}{g ∙ f} 〉
        ⌊ g ∙ f ⌋ ∙ ⌊ f ⌋
      ∼〈 R3 {f = f}{g ∙ f} 〉
        ⌊ (g ∙ f) ∙ ⌊ f ⌋ ⌋ 
      ∼〈 cong-rest (sym∼ (assoc∙ {f = ⌊ f ⌋})) 〉
        ⌊ g ∙ (f ∙ ⌊ f ⌋) ⌋ 
      ∼〈 cong-rest (g ∙∼ (R1 {f = f})) 〉
        ⌊ g ∙ f ⌋
      qed

_sem-⊕_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A ⊎ B) ≃₁ (C ⊎ D)
_sem-⊕_ {A}{B}{C}{D} (f , pinv f† i1 i2)  (g , pinv g† j1 j2) = h , (pinv h† α β)
  where
    open Eq≈
    h : A ⊎ B → Delay (C ⊎ D)
    h = [ mapD inj₁ ∘  f , mapD inj₂ ∘ g ]′

    h† : C ⊎ D → Delay (A ⊎ B)
    h† = [ mapD inj₁ ∘  f† , mapD inj₂ ∘ g† ]′

    α : h ∙ h† ∼ ⌊ h† ⌋
    α (inj₁ c) =
      proof
        bindD [ mapD inj₁ ∘  f , mapD inj₂ ∘ g ]′ (mapD inj₁ (f† c))
      ≈〈 M3 (f† c) 〉
        bindD (mapD inj₁ ∘ f) (f† c)
      ≈〈 sym≈ (M3 (f† c)) 〉
        bindD (λ x → now (inj₁ x)) (bindD f (f† c))
      ≈〈 cong-bindD (i1 c) 〉
        bindD (λ x → now (inj₁ x)) (bindD (λ _ → now c) (f† c))
      ≈〈 M3 (f† c) 〉
        bindD (λ x → now (inj₁ c)) (f† c)
      ≈〈 sym≈ (M3 (f† c)) 〉
--        bindD (λ x → now (proj₁ x)) (bindD (λ x → now (inj₁ c , inj₁ x)) (f† c))
--      ≈〈 cong-bindD (sym≈ (M3 (f† c))) 〉
        bindD (λ _ → now (inj₁ c)) (bindD (λ x → now (inj₁ x)) (f† c))
      qed      
    α (inj₂ d) = 
      proof
        bindD [ mapD inj₁ ∘  f , mapD inj₂ ∘ g ]′ (mapD inj₂ (g† d))
      ≈〈 M3 (g† d) 〉
        bindD (mapD inj₂ ∘ g) (g† d)
      ≈〈 sym≈ (M3 (g† d)) 〉
        bindD (λ x → now (inj₂ x)) (bindD g (g† d))
      ≈〈 cong-bindD (j1 d) 〉
        bindD (λ x → now (inj₂ x)) (bindD (λ _ → now d) (g† d))
      ≈〈 M3 (g† d) 〉
        bindD (λ x → now (inj₂ d)) (g† d)
      ≈〈 sym≈ (M3 (g† d)) 〉
--        bindD (λ x → now (proj₁ x)) (bindD (λ x → now (inj₂ d , inj₂ x)) (g† d))
--      ≈〈 cong-bindD (sym≈ (M3 (g† d))) 〉
        bindD (λ _ → now (inj₂ d)) (bindD (λ x → now (inj₂ x)) (g† d))
      qed      

    β : h† ∙ h ∼ ⌊ h ⌋
    β (inj₁ a) =
      proof
        bindD [ mapD inj₁ ∘  f† , mapD inj₂ ∘ g† ]′ (mapD inj₁ (f a))
      ≈〈 M3 (f a) 〉
        bindD (mapD inj₁ ∘ f†) (f a)
      ≈〈 sym≈ (M3 (f a)) 〉
        bindD (λ x → now (inj₁ x)) (bindD f† (f a))
      ≈〈 cong-bindD (i2 a) 〉
--        bindD (λ x → now (inj₁ x)) (bindD (λ x → now (proj₁ x)) (bindD (λ x → now (a , x)) (f a)))
--      ≈〈 cong-bindD (M3 (f a)) 〉
        bindD (λ x → now (inj₁ x)) (bindD (λ x → now a) (f a))
      ≈〈 M3 (f a) 〉
        bindD (λ x → now (inj₁ a)) (f a)
      ≈〈 sym≈ (M3 (f a)) 〉
--        bindD (λ x → now (proj₁ x)) (bindD (λ x → now (inj₁ a , inj₁ x)) (f a))
--      ≈〈 cong-bindD (sym≈ (M3 (f a))) 〉
        bindD (λ _ → now (inj₁ a)) (bindD (λ x → now (inj₁ x)) (f a))
      qed      
    β (inj₂ b) = 
      proof
        bindD [ mapD inj₁ ∘  f† , mapD inj₂ ∘ g† ]′ (mapD inj₂ (g b))
      ≈〈 M3 (g b) 〉
        bindD (mapD inj₂ ∘ g†) (g b)
      ≈〈 sym≈ (M3 (g b)) 〉
        bindD (λ x → now (inj₂ x)) (bindD g† (g b))
      ≈〈 cong-bindD (j2 b) 〉
--        bindD (λ x → now (inj₂ x)) (bindD (λ x → now (proj₁ x)) (bindD (λ x → now (b , x)) (g b)))
--      ≈〈 cong-bindD (M3 (g b)) 〉
        bindD (λ x → now (inj₂ x)) (bindD (λ x → now b) (g b))
      ≈〈 M3 (g b) 〉
        bindD (λ x → now (inj₂ b)) (g b)
      ≈〈 sym≈ (M3 (g b)) 〉
--        bindD (λ x → now (proj₁ x)) (bindD (λ x → now (inj₂ b , inj₂ x)) (g b))
--      ≈〈 cong-bindD (sym≈ (M3 (g b))) 〉
        bindD (λ _ → now (inj₂ b)) (bindD (λ x → now (inj₂ x)) (g b))
      qed      

_sem-⊗_ : ∀ {A B C D} → A ≃₁ C → B ≃₁ D → (A × B) ≃₁ (C × D)
_sem-⊗_ {A}{B}{C}{D} (f , pinv f† i1 i2) (g , pinv g† j1 j2) = h , (pinv h† {!!} {!!})
  where
    open Eq∼
    h : A × B → Delay (C × D)
    h = costr ∙ str ∘ map× f g --bindD (λ c → bindD (λ d → now (c , d)) (g b)) (f a)

    h† : C × D → Delay (A × B)
    h† = str ∙ costr ∘ map× f† g† --(c , d) = bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d)

    α : h ∙ h† ∼ ⌊ h† ⌋
    α =
      proof
        (costr ∙ str ∘ map× f g) ∙ (str ∙ costr ∘ map× f† g†)
      ∼〈 {!!} 〉
        (costr ∙ str ∘ map× f g) ∙ (str ∙ (costr ∘ map× id g†) ∘ map× f† id)
      ∼〈 {!!} 〉
        (costr ∙ str ∘ map× f g) ∙ (str ∙ (mapD (map× id g†) ∘ costr) ∘ map× f† id)
      ∼〈 {!!} 〉
        (costr ∙ str ∘ map× f g) ∙ ((str ∙ mapD (map× id g†)) ∘ costr ∘ map× f† id)
      ∼〈 {!!} 〉
        mapD proj₁ ∘ str ∘ < id , str ∙ costr ∘ map× f† g† >
      ∼〈 {!!} 〉
        ⌊ h† ⌋
      qed

{-
    h : A × B → Delay (C × D)
    h (a , b) = bindD (λ c → bindD (λ d → now (c , d)) (g b)) (f a)

    h† : C × D → Delay (A × B)
    h† (c , d) = bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d)

    α : h ∙ h† ∼ ⌊ h† ⌋
    α (c , d) =
      proof
        bindD h (bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d))
      ≈〈 {!!} 〉
        bindD (λ b → bindD h (bindD (λ a → now (a , b)) (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (bindD (λ c → bindD (λ d → now (c , d)) (g b)) ∘ f) (f† c)) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ c → bindD (λ d → now (c , d)) (g b)) (bindD f (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ c' → bindD (λ d' → now (c' , d')) (g b)) (bindD (λ _ → now c) (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ _ → bindD (λ d' → now (c , d')) (g b)) (f† c)) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ _ → now (c , d)) (f† c)) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ _ → now (c , d)) (bindD (λ a → now (a , b)) (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ _ → now (c , d)) (bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d))
      qed
-}

{-
    α : h ∙ h† ∼ ⌊ h† ⌋
    α (c , d) =
      proof
        bindD h (bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d))
      ≈〈 {!!} 〉
        bindD (λ b → bindD h (bindD (λ a → now (a , b)) (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (bindD (λ c → bindD (λ d → now (c , d)) (g b)) ∘ f) (f† c)) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ c → bindD (λ d → now (c , d)) (g b)) (bindD f (f† c))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ c' → bindD (λ d' → now (c' , d')) (g b)) (bindD (λ x → now (proj₁ x)) (bindD (λ x → now (c , x)) (f† c)))) (g† d)
      ≈〈 {!!} 〉
        bindD (λ b → bindD (λ c' → bindD (λ d' → now (c' , d')) (g b)) (bindD (λ x → now (proj₁ x)) (bindD (λ x → now (c , x)) (f† c)))) (g† d)
      ≈〈 {!!} 〉
--        bindD (λ x → now (proj₁ x)) (bindD (λ a → now ((c , d) , bindD (λ b → now (a , b)) (g† d)) ) (f† c))
--      ≈〈 {!!} 〉
        bindD (λ x → now (proj₁ x)) (bindD (λ x → now ((c , d) , x)) (bindD (λ b → bindD (λ a → now (a , b)) (f† c)) (g† d)))
      qed
-}


sem-fold-f : ∀ ρ ρ' → ⟦ decode ρ' (μ ρ) ⟧U → sem-decode ⟦ ρ' ⟧Ucode (Mu ⟦ ρ ⟧Ucode)
sem-fold-f ρ (ℂ τ) = id
sem-fold-f ρ 𝕀 = id
sem-fold-f ρ (ρ₁ ⊕ ρ₂) = map⊎ (sem-fold-f ρ ρ₁) (sem-fold-f ρ ρ₂)
sem-fold-f ρ (ρ₁ ⊗ ρ₂) = map× (sem-fold-f ρ ρ₁) (sem-fold-f ρ ρ₂)

sem-fold-g : ∀ ρ ρ' → sem-decode ⟦ ρ' ⟧Ucode (Mu ⟦ ρ ⟧Ucode) → ⟦ decode ρ' (μ ρ) ⟧U
sem-fold-g ρ (ℂ τ) = id
sem-fold-g ρ 𝕀 = id
sem-fold-g ρ (ρ₁ ⊕ ρ₂) = map⊎ (sem-fold-g ρ ρ₁) (sem-fold-g ρ ρ₂)
sem-fold-g ρ (ρ₁ ⊗ ρ₂) = map× (sem-fold-g ρ ρ₁) (sem-fold-g ρ ρ₂)

sem-fold-α : ∀ ρ ρ' x → sem-fold-f ρ ρ' (sem-fold-g ρ ρ' x) ≡ x
sem-fold-α ρ (ℂ τ) x = refl
sem-fold-α ρ 𝕀 x = refl
sem-fold-α ρ (ρ' ⊕ ρ'') (inj₁ x) = cong inj₁ (sem-fold-α ρ ρ' x)
sem-fold-α ρ (ρ' ⊕ ρ'') (inj₂ y) = cong inj₂ (sem-fold-α ρ ρ'' y)
sem-fold-α ρ (ρ' ⊗ ρ'') (x , y) = cong₂ _,_ (sem-fold-α ρ ρ' x) (sem-fold-α ρ ρ'' y)

sem-fold-β : ∀ ρ ρ' x → sem-fold-g ρ ρ' (sem-fold-f ρ ρ' x) ≡ x
sem-fold-β ρ (ℂ τ) x = refl
sem-fold-β ρ 𝕀 x = refl
sem-fold-β ρ (ρ' ⊕ ρ'') (inj₁ x) = cong inj₁ (sem-fold-β ρ ρ' x)
sem-fold-β ρ (ρ' ⊕ ρ'') (inj₂ y) = cong inj₂ (sem-fold-β ρ ρ'' y)
sem-fold-β ρ (ρ' ⊗ ρ'') (x , y) = cong₂ _,_ (sem-fold-β ρ ρ' x) (sem-fold-β ρ ρ'' y)


sem-fold : ∀ ρ → ⟦ decode ρ (μ ρ) ⟧U ≅ Mu ⟦ ρ ⟧Ucode
sem-fold ρ = f , tinv g α β
  where
    f : ⟦ decode ρ (μ ρ) ⟧U → Mu ⟦ ρ ⟧Ucode
    f = sup ∘ sem-fold-f ρ ρ

    g : Mu ⟦ ρ ⟧Ucode → ⟦ decode ρ (μ ρ) ⟧U
    g (sup x) = sem-fold-g ρ ρ x

    α : ∀ x → f (g x) ≡ x
    α (sup x) = cong sup (sem-fold-α ρ ρ x)

    β : ∀ x → g (f x) ≡ x
    β = sem-fold-β ρ ρ

sem-trace : ∀ {A B U} → (U ⊎ A) ≃₁ (U ⊎ B) → A ≃₁ B
sem-trace (f , pinv f† i1 i2) = traceD f , pinv (traceD f†) α β
  where
    α : traceD f ∙ traceD f† ∼ ⌊ traceD f† ⌋
    α = linv-equiv₂ _ _ (λ p → traceD-now-equiv₂ f (reverse-trace-reach f† f (linv-equiv₁ f† f i1) (traceD-now-equiv₁ f† p)))

    β : traceD f† ∙ traceD f ∼ ⌊ traceD f ⌋
    β = linv-equiv₂ _ _ (λ p → traceD-now-equiv₂ f† (reverse-trace-reach f f† (linv-equiv₁ f f† i2) (traceD-now-equiv₁ f p)))

⟦ : ∀ {τ₁ τ₂} → τ₁ ⟷ τ₂ → ⟦ τ₁ ⟧U ≃₁ ⟦ τ₂ ⟧U
⟦ id⟷ = total-to-partial-inv sem-id⟷
⟦ unite⊕l = sem-unite⊕l
⟦ uniti⊕l = sem-dagger sem-unite⊕l
⟦ swap⊕ = sem-swap⊕
⟦ assocλ⊕ = sem-assocλ⊕
⟦ assocr⊕ = sem-dagger sem-assocλ⊕
⟦ unite⊗l = sem-unite⊗l
⟦ uniti⊗l = sem-dagger sem-unite⊗l 
⟦ swap⊗ = sem-swap⊗
⟦ assocλ⊗ = sem-assocλ⊗
⟦ assocr⊗ = sem-dagger sem-assocλ⊗ 
⟦ absorbr = sem-absorbr
⟦ factorzl = sem-dagger sem-absorbr
⟦ dist = sem-dist
⟦ factor = sem-dagger sem-dist
⟦ (f ⊙ g) = (⟦ f) sem-⊙ (⟦ g)
⟦ (f ⊕ g) = (⟦ f) sem-⊕ (⟦ g)
⟦ (f ⊗ g) = (⟦ f) sem-⊗ (⟦ g)
⟦ (fold ρ) = total-to-partial-inv (sem-fold ρ)
⟦ (unfold ρ) = sem-dagger (total-to-partial-inv (sem-fold ρ))
⟦ (trace p) = sem-trace (⟦ p)


-}
