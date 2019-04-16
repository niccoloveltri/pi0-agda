{-# OPTIONS --without-K #-}

module delay.Structure where

open import Data.Product renaming (map to map×)
open import Function

open import delay.Delay
open import delay.Monad

-- Products

θ : ∀ {A B} → Delay A × Delay B → Delay (A × B)
θ = costr ∙ str

θ2 : ∀ {A B} → Delay A × Delay B → Delay (A × B)
θ2 = str ∙ costr

θ↓₁ : ∀ {A B} (x : Delay A × Delay B) {a : A}{b : B} → θ x ↓ (a , b) → θ2 x ↓ (a , b)
θ↓₁ (x , y) {a}{b} p = trans≈ (cong-bindD (cong-bindD (proj₂ q))) (cong-bindD (proj₁ q))
  where
    q : y ↓ b × x ↓ a
    q with bindD↓ costr (bindD (λ z → now (x , z)) y) p
    q | (z , b) , r , r' with bindD↓ (λ z₁ → now (x , z₁)) y r
    q | (x , b) , r , r' | .b , s , now with bindD↓ (λ z → now (z , b)) x r'
    q | (x , b) , r , r' | .b , s , now | b' , t , now = s , t

θ↓₂ : ∀ {A B} (x : Delay A × Delay B) {a : A}{b : B} → θ2 x ↓ (a , b) → θ x ↓ (a , b)
θ↓₂ (x , y) {a}{b} p = trans≈ (cong-bindD (cong-bindD (proj₁ q))) (cong-bindD (proj₂ q))
  where
    q : y ↓ b × x ↓ a
    q with bindD↓ str (bindD (λ z → now (z , y)) x) p
    q | (z , a') , r , r' with bindD↓ (λ z₁ → now (z₁ , y)) x r
    q | (z , a') , r , r' | .z , s , now with bindD↓ (λ z₁ → now (z , z₁)) y r'
    q | (z , a') , r , r' | .z , s , now | b' , t , now = t , s

θ-eq : ∀ {A B} (x : Delay A × Delay B) → θ x ≈ θ2 x
θ-eq x = ≈-equiv₂ ((θ↓₁ x) , θ↓₂ x)

_×D_ : {A B C D : Set} (f : A → Delay C) (g : B → Delay D) → A × B → Delay (C × D)
f ×D g = θ ∘ map× f g

_×D2_ : {A B C D : Set} (f : A → Delay C) (g : B → Delay D) → A × B → Delay (C × D)
f ×D2 g = θ2 ∘ map× f g

eq-×D : {A B C D : Set} (f : A → Delay C) (g : B → Delay D) → f ×D g ∼ f ×D2 g
eq-×D f g x = cong-app-bindD (now (map× f g x)) θ-eq

cong-θ : ∀ {A B} {x x' : Delay A} {y y' : Delay B}
  → x ≈ x' → y ≈ y' → θ (x , y) ≈ θ (x' , y')
cong-θ {x = x}{x'}{_}{y'} p q =
  trans≈ (cong-bindD (cong-bindD q))
    (trans≈ (θ-eq (x , y'))
      (trans≈ (cong-bindD (cong-bindD p))
        (sym≈ (θ-eq (x' , y')))))  
