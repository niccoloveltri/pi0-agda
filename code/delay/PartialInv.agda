{-# OPTIONS --without-K #-}

module delay.PartialInv where

open import Data.Product renaming (map to map×)
open import Data.Sum
open import Function 
open import Relation.Binary.PropositionalEquality
open import Size

open import Utilities
open import delay.Delay
open import delay.Monad
open import delay.Elgot
open import delay.Structure

-- Partial equivalences

record is-partial-inv {A B : Set} (f : A → Delay B) : Set where
  constructor pinv
  field
    g : B → Delay A
    α : ∀ a b → g b ↓ a → f a ↓ b
    β : ∀ b a → f a ↓ b → g b ↓ a

_≃₁_ : Set → Set → Set
A ≃₁ B = Σ (A → Delay B) is-partial-inv

-- Semantic dagger operation

sem-dagger : ∀{A B} → A ≃₁ B → B ≃₁ A
sem-dagger (f , pinv g α β) = g , (pinv f β α)

-- Equivalence of partial equivalences

_≃₂_ : ∀ {A B} → A ≃₁ B → A ≃₁ B → Set
(f , _) ≃₂ (g , _) = f ∼ g

-- Our definition is logically equivalent to the one given in inverse
-- categories.

pinv-eq↓₁ : {A B : Set} {f : A → Delay B} {g : B → Delay A}
  → (∀ b a → f a ↓ b → g b ↓ a)
  → ∀ {b} a → ((f ∙ g) ∙ f) a ↓ b → f a ↓ b
pinv-eq↓₁ {f = f}{g} p a q with bindD↓ (bindD f ∘ g) (f a) q
... | b , r , r' with bindD↓ f (g b) r'
... | a' , s , s' with unique↓ (p _ _ r) s
pinv-eq↓₁ {f = f} {g} p .a q | b , r , r' | a , s , s' | refl = s'  

pinv-eq↓₂ : {A B : Set} {f : A → Delay B} {g : B → Delay A}
  → (∀ b a → f a ↓ b → g b ↓ a)
  → ∀ {b} a → f a ↓ b → ((f ∙ g) ∙ f) a ↓ b 
pinv-eq↓₂ {f = f}{g} p a q =
  trans≈ (cong-bindD q) (trans≈ (cong-bindD (p _ _ q)) q)

pinv-eq : {A B : Set} {f : A → Delay B} {g : B → Delay A}
  → (∀ b a → f a ↓ b → g b ↓ a)
  → (f ∙ g) ∙ f ∼ f
pinv-eq p x = ≈-equiv₂ (pinv-eq↓₁ p x , pinv-eq↓₂ p x)

-- Semantic uniqueness of partial inverse

pinv-u↓ : {A B C : Set}
  → {f : A → Delay B} {g : B → Delay A}
  → {h : C → Delay B} {k : B → Delay C}
  → (∀ a b → g b ↓ a → f a ↓ b)
  → (∀ c b → k b ↓ c → h c ↓ b)
  → ∀ {b} x → (((f ∙ g) ∙ h) ∙ k) x ↓ b → (((h ∙ k) ∙ f) ∙ g) x ↓ b
pinv-u↓ {f = f}{g}{h}{k} p p' x q with bindD↓ (λ z → bindD (λ y → bindD f (g y)) (h z)) (k x) q
... | c , r , r' with bindD↓ (λ y → bindD f (g y)) (h c) r'
... | b' , s , s' with bindD↓ f (g b') s'
... | a , t , t' with unique↓ (p' _ _ r) s
pinv-u↓ {f = f} {g} {h} {k} p p' .b q | c , r , r' | b , s , s' | a , t , t' | refl with unique↓ (p _ _ t) t'
pinv-u↓ {f = f} {g} {h} {k} p p' .b q | c , r , r' | b , s , s' | a , t , t' | refl | refl =
    trans≈ (cong-bindD t) (trans≈ (cong-bindD t') (trans≈ (cong-bindD r) s))  

pinv-u : {A B C : Set}
  → {f : A → Delay B} {g : B → Delay A}
  → {h : C → Delay B} {k : B → Delay C}
  → (∀ a b → g b ↓ a → f a ↓ b)
  → (∀ c b → k b ↓ c → h c ↓ b)
  → ((f ∙ g) ∙ h) ∙ k ∼ ((h ∙ k) ∙ f) ∙ g
pinv-u p q x = ≈-equiv₂ (pinv-u↓ p q x , pinv-u↓ q p x)  
  

-- Total isomorphisms embed in partial isomorphisms

≅-to-≃₁ : ∀ {A B} → A ≅ B → A ≃₁ B
≅-to-≃₁ (f , tinv g α β) = now ∘ f ,
  (pinv (now ∘ g)
        (λ { _ _ now → subst (λ x → now (f (g _)) ↓ x) (α _) now })
        (λ { _ _ now → subst (λ x → now (g (f _)) ↓ x) (β _) now }))

-- Semantic sequential composition 

_⊙≃₁_ : ∀ {A B C} → B ≃₁ C → A ≃₁ B → A ≃₁ C
(g , pinv g† i1 i2) ⊙≃₁ (f , pinv f† j1 j2) = (g ∙ f) , pinv (f† ∙ g†) α β
  where
    α : ∀ a c → bindD f† (g† c) ↓ a → bindD g (f a) ↓ c
    α a c p with bindD↓ f† (g† c) p
    ... | b , q , r = trans≈ (bindD-input↓ g (j1 a b r)) (i1 b c q) 

    β : ∀ c a → bindD g (f a) ↓ c → bindD f† (g† c) ↓ a
    β c a p with bindD↓ g (f a) p
    ... | b , q , r = trans≈ (bindD-input↓ f† (i2 c b r)) (j2 b a q)


-- Semantic counterparts of ⊕ and ⊗ 

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
_⊗≃₁_ {A}{B}{C}{D} (f , pinv f† i1 i2) (g , pinv g† j1 j2) = f ×D g , pinv (f† ×D g†) α β
  where
    α : (a : A × B) (b : C × D) → (f† ×D g†) b ↓ a → (f ×D g) a ↓ b
    α (a , b) (c , d) p with bindD↓ costr (bindD (λ x → now (f† c , x)) (g† d)) p
    ... | ((x , b') , q , q') with bindD↓ (λ z → now (f† c , z)) (g† d) q
    α (a , b) (c , d) p | (.(f† c) , b') , q , q' | .b' , r , now with bindD↓ (λ x → now (x , b')) (f† c) q'
    α (a , .b') (c , d) p | (.(f† c) , b') , q , q' | .b' , r , now | .a , s , now =
      trans≈ (cong-bindD (bindD-input↓ (λ x → now (f a , x)) (j1 _ _ r)))
             (bindD-input↓ (λ x → now (x , d)) (i1 _ _ s))

    β : (b : C × D) (a : A × B) → (f ×D g) a ↓ b → (f† ×D g†) b ↓ a
    β (c , d) (a , b) p with bindD↓ costr (bindD (λ x → now (f a , x)) (g b)) p
    ... | ((x , d') , q , q') with bindD↓ (λ z → now (f a , z)) (g b) q
    β (c , d) (a , b) p | (.(f a) , d') , q , q' | .d' , r , now with bindD↓ (λ x → now (x , d')) (f a) q'
    β (c , .d') (a , b) p | (.(f a) , d') , q , q' | .d' , r , now | .c , s , now =
      trans≈ (cong-bindD (bindD-input↓ (λ x → now (f† c , x)) (j2 _ _ r)))
             (bindD-input↓ (λ x → now (x , b)) (i2 _ _ s))

-- Semantic trace

trace≃₁ : ∀ {A B U} → (U ⊎ A) ≃₁ (U ⊎ B) → A ≃₁ B
trace≃₁ (f , pinv f† i1 i2) = traceD f , pinv (traceD f†) α β
  where
    α : ∀ a b → traceD f† b ↓ a → traceD f a ↓ b 
    α a b p = traceD-now-equiv₂ f (reverse-trace-Orb f† f i1 (traceD-now-equiv₁ f† p))

    β : ∀ b a → traceD f a ↓ b → traceD f† b ↓ a 
    β b a p = traceD-now-equiv₂ f† (reverse-trace-Orb f f† i2 (traceD-now-equiv₁ f p))

