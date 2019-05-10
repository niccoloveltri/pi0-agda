{-# OPTIONS --without-K #-}

module delay.Structure where

open import Data.Product renaming (map to map×)
open import Data.Sum
open import Function

open import delay.Delay
open import delay.Monad

-- Partial products

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


fun∙×D : {A B C D E F : Set}
  → {f : A → Delay B} {g : B → Delay C}
  → {h : D → Delay E} {k : E → Delay F}
  → ((g ∙ f) ×D (k ∙ h)) ∼ (g ×D k) ∙ (f ×D h)
fun∙×D {B = B}{F = F} {f = f}{g}{h}{k} (a , d) =
  trans≈ (M3 (bindD k (h d)))
    (trans≈ (M3 (h d))
      (trans≈ (cong-app-bindD (h d)
                              (λ e → trans≈ (≈-equiv₂ ((lem₁ (f a) (k e)) , (lem₂ (f a) (k e))))
                                       (sym≈ (M3 (f a)))))
        (trans≈ (sym≈ (M3 (h d)))
          (trans≈ (cong-app-bindD (bindD (λ x → bindD (λ x₁ → now (x₁ , x)) (f a)) (h d))
                                  (λ x → sym≈ (M3 (k (proj₂ x)))))
            (sym≈ (cong-bindD (M3 (h d))))))))
  where
    lem₁ : ∀ {z} (u : Delay B) (v : Delay F)
      → bindD (λ x → bindD (λ y → now (y , x)) (bindD g u)) v ↓ z
      → bindD (λ x → bindD (λ y → bindD (λ z → now (z , y)) (g x)) v) u ↓ z
    lem₁ u v p with bindD↓ (λ x → bindD (λ y → now (y , x)) (bindD g u)) v p
    lem₁ u v p | (x , q , q') with bindD↓ (λ y → now (y , x)) (bindD g u) q'
    lem₁ u v p | x , q , q' | c , r , now with bindD↓ g u r
    ... | b , s , s' =
      trans≈ (bindD-input↓ (λ x₁ → bindD (λ y → bindD (λ z → now (z , y)) (g x₁)) v) s)
        (trans≈ (bindD-input↓ (λ y → bindD (λ z → now (z , y)) (g b)) q)
          (bindD-input↓ (λ z → now (z , x)) s'))

    lem₂ : ∀ {z} (u : Delay B) (v : Delay F)
      → bindD (λ x → bindD (λ y → bindD (λ z → now (z , y)) (g x)) v) u ↓ z
      → bindD (λ x → bindD (λ y → now (y , x)) (bindD g u)) v ↓ z
    lem₂ u v p with bindD↓ (λ x → bindD (λ y → bindD (λ z₁ → now (z₁ , y)) (g x)) v) u p
    ... | (b , q , q') with bindD↓ (λ y → bindD (λ z₁ → now (z₁ , y)) (g b)) v q'
    ... | (x , r , r') with bindD↓ (λ z₁ → now (z₁ , x)) (g b) r'
    lem₂ u v p | b , q , q' | x , r , r' | c , s , now =
      trans≈ (bindD-input↓ (λ x₁ → bindD (λ y → now (y , x₁)) (bindD g u)) r)
        (trans≈ (cong-bindD (bindD-input↓ g q))
          (bindD-input↓ (λ y → now (y , x)) s))

-- Coproducts

copair∼ : {A B C : Set} {f f' : A → Delay C} {g g' : B → Delay C}
  → f ∼ f' → g ∼ g' → [ f , g ]′ ∼ [ f' , g' ]′
copair∼ p q (inj₁ x) = p x
copair∼ p q (inj₂ y) = q y  

map⊎D : {A B C D : Set} (f : A → Delay C) (g : B → Delay D)
  → A ⊎ B → Delay (C ⊎ D)
map⊎D f g = [ mapD inj₁ ∘  f , mapD inj₂ ∘ g ]′
