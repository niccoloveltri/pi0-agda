{-# OPTIONS --without-K #-}

module delay.Elgot where

open import Data.Sum renaming (map to map⊎)
open import Data.Product
open import Data.Nat
open import Data.Empty
open import Function 
open import Relation.Binary.PropositionalEquality hiding (naturality)

open import Utilities
open import delay.Delay
open import delay.Monad
open import delay.Structure

-- Elgot iteration

mutual
  iterD' : {A C : Set} → (A → Delay (A ⊎ C))
    → Delay (A ⊎ C) → Delay C
  iterD' f (now (inj₁ x)) = later (∞iterD' f (f x))
  iterD' f (now (inj₂ x)) = now x
  iterD' f (later x) = later (∞iterD' f (force x))

  ∞iterD' : {A C : Set} → (A → Delay (A ⊎ C))
    → Delay (A ⊎ C) → ∞Delay C
  force (∞iterD' f x) = iterD' f x

iterD : {A C : Set} → (A → Delay (A ⊎ C))
    → A → Delay C
iterD f x = iterD' f (f x)    

-- Iteration preserves weak bisimilarity

mutual
  cong-iterD' : ∀ {i} {A C}  (f : A → Delay (A ⊎ C))
    → {x y : Delay (A ⊎ C)} → [ i ] x ≈' y → [ i ] iterD' f x ≈' iterD' f y
  cong-iterD' f (now {inj₁ x}) = later (∞cong-iterD' f ∞refl≈)
  cong-iterD' f (now {inj₂ y}) = now
  cong-iterD' f (later p) = later (∞cong-iterD' f p)
  cong-iterD' f (laterL p) = laterL (cong-iterD' f p)
  cong-iterD' f (laterR p) = laterR (cong-iterD' f p)  

  ∞cong-iterD' : ∀ {i} {A C}  (f : A → Delay (A ⊎ C))
    → {x y : Delay (A ⊎ C)} → [ i ] x ∞≈' y → [ i ] iterD' f x ∞≈' iterD' f y
  force (∞cong-iterD' f p) = cong-iterD' f (force p)

mutual
  cong-iterD'' : ∀ {A C}  {f f' : A → Delay (A ⊎ C)} → f ∼ f'
    → {x y : Delay (A ⊎ C)} → x ≈ y → iterD' f x ≈ iterD' f' y
  cong-iterD'' p (now {inj₁ x}) = later (∞cong-iterD'' p (p x))
  cong-iterD'' p (now {inj₂ y}) = now
  cong-iterD'' p (later x) = later (∞cong-iterD'' p (force x))
  cong-iterD'' p (laterL q) = laterL (cong-iterD'' p q)
  cong-iterD'' p (laterR q) = laterR (cong-iterD'' p q)

  ∞cong-iterD'' : ∀ {A C}  {f f' : A → Delay (A ⊎ C)} → f ∼ f'
    → {x y : Delay (A ⊎ C)} → x ≈ y → iterD' f x ∞≈ iterD' f' y
  force (∞cong-iterD'' p q) = cong-iterD'' p q

cong-iterD : ∀ {A C} {f f' : A → Delay (A ⊎ C)} → f ∼ f'
  → iterD f ∼ iterD f'
cong-iterD p x = cong-iterD'' p (p x)

-- Trace operator

_L : {A B C : Set} → (A ⊎ B → C) → A → C
f L = f ∘ inj₁

_R : {A B C : Set} → (A ⊎ B → C) → B → C
f R = f ∘ inj₂

traceD : {A B U : Set} → (U ⊎ A → Delay (U ⊎ B)) → A → Delay B
traceD f = bindD [ iterD (f L) , now ]′ ∘ (f R)



-- We need to prove that traceD is a dagger trace, meaning that dagger
-- (traceD f) is equal to traceD (dagger f).

-- In order to show this, we introduce the notion of orbit.  An
-- element y : U ⊎ B is in the orbit of x : U ⊎ A wrt. f if y is
-- obtained from x after a finite number of applications of the
-- function f.

data Orb {A B U : Set} (f : U ⊎ A → Delay (U ⊎ B)) : U ⊎ A → U ⊎ B → Set where
  done : ∀ {x y} → f x ↓ y → Orb f x y
  step : ∀ {x u y} → f x ↓ (inj₁ u) → Orb f (inj₁ u) y → Orb f x y

-- We can talk about orbit for iteration and for trace.

iter-Orb : {A B : Set} (f : A → Delay (A ⊎ B)) → A → B → Set
iter-Orb {A}{B} f a b = Orb [ f , (λ z → now (inj₂ z)) ]′ (inj₁ a) (inj₂ b)

trace-Orb : {A B U : Set} (f : U ⊎ A → Delay (U ⊎ B)) → A → B → Set
trace-Orb f a b = Orb f (inj₂ a) (inj₂ b)

-- The fact that traceD f a converges to b is equivalent to (inj₂ b)
-- being the last element in the orbit of (inj₂ a) wrt. f

iterD-now-Orb : ∀ {A B} (f : A → Delay (A ⊎ B)) {a} {b}
  → (x : Delay (A ⊎ B)) (q : f a ≈ x)
  → (p : iterD' f x ↓ b) → iter-Orb f a b 
iterD-now-Orb f (now (inj₁ a')) q (laterL p) =
  step q (iterD-now-Orb f (f a') refl≈ p)
iterD-now-Orb f (now (inj₂ b)) q now = done q
iterD-now-Orb f (later x) q (laterL p) =
  iterD-now-Orb f (force x) (laterR-1 q) p  

iterD-now-equiv₁ : ∀ {A B} (f : A → Delay (A ⊎ B)) {a} {b}
  → iterD f a ↓ b → iter-Orb f a b
iterD-now-equiv₁ f p = iterD-now-Orb f _ refl≈ p

iterD-now-equiv₂ : ∀ {A B} (f : A → Delay (A ⊎ B)) {a : A} {b : B}
  → iter-Orb f a b → iterD f a ↓ b
iterD-now-equiv₂ f (done p) = cong-iterD' f p
iterD-now-equiv₂ f (step p q) =
  trans≈ (cong-iterD' f p) (laterL (iterD-now-equiv₂ f q))

traceD-now-equiv₁ : ∀ {A B U} (f : U ⊎ A → Delay (U ⊎ B)) {a} {b}
  → traceD f a ↓ b → trace-Orb f a b
traceD-now-equiv₁ f p with bindD↓ [ iterD (f L) , now ]′ (f (inj₂ _)) p
traceD-now-equiv₁ f p | inj₂ b , q , now = done q
traceD-now-equiv₁ f p | inj₁ u , q , r = step q (lem (iterD-now-equiv₁ (f L) r))
  where
    lem : ∀ {x y} → Orb [ (f L) , (λ z → now (inj₂ z)) ]′ (inj₁ x) y → Orb f (inj₁ x) y
    lem (done s) = done s
    lem (step s t) = step s (lem t)

traceD-now-equiv₂ : ∀ {A B U} (f : U ⊎ A → Delay (U ⊎ B)) {a} {b}
  → trace-Orb f a b → traceD f a ↓ b
traceD-now-equiv₂ f (done p) = cong-bindD p
traceD-now-equiv₂ f (step p q) =
  trans≈ (cong-bindD p) (iterD-now-equiv₂ (f L) (lem q))
  where
    lem : ∀ {x y} → Orb f (inj₁ x) y → Orb [ (f L) , (λ z → now (inj₂ z)) ]′ (inj₁ x) y
    lem (done s) = done s
    lem (step s t) = step s (lem t)

-- If the function f has a left partial inverse g, then (inj₂ b) is
-- the last element of the orbit of (inj₂ a) wrt. f implies that (inj₂
-- a) is the last element of the orbit of (inj₂ b) wrt. f

reverse-trace-Orb' : ∀ {A B U} (f : U ⊎ A → Delay (U ⊎ B)) (g : U ⊎ B → Delay (U ⊎ A))
  → (∀ x y → f y ↓ x → g x ↓ y)
  → ∀ {a u b} → Orb f (inj₁ u) (inj₂ b) → Orb g (inj₁ u) (inj₂ a) → Orb g (inj₂ b) (inj₂ a) 
reverse-trace-Orb' f g p (done q) r = step (p _ _ q) r
reverse-trace-Orb' f g p (step q q') r = reverse-trace-Orb' f g p q' (step (p _ _ q) r)

reverse-trace-Orb : ∀ {A B U} (f : U ⊎ A → Delay (U ⊎ B)) (g : U ⊎ B → Delay (U ⊎ A))
  → (∀ x y → f y ↓ x → g x ↓ y)
  → ∀ {a b} → trace-Orb f a b → trace-Orb g b a
reverse-trace-Orb f g p (done q) = done (p _ _ q)
reverse-trace-Orb f g p (step q r) = reverse-trace-Orb' f g p r (done (p _ _ q))

-- Fixpoint axiom

mutual
  fixpoint' : ∀ {A C} (f : A → Delay (A ⊎ C)) → bindD [ iterD f , now ]′ ∼ iterD' f
  fixpoint' f (now (inj₁ x)) = laterR refl≈
  fixpoint' f (now (inj₂ x)) = refl≈
  fixpoint' f (later x) = later (∞fixpoint' f (force x))

  ∞fixpoint' : ∀ {A C} (f : A → Delay (A ⊎ C)) (x : Delay (A ⊎ C)) → 
             bindD [ iterD f , now ]′ x ∞≈ iterD' f x
  force (∞fixpoint' f x) = fixpoint' f x

fixpoint : ∀ {A C} (f : A → Delay (A ⊎ C)) → [ iterD f , now ]′ ∙ f ∼ iterD f
fixpoint f x = fixpoint' f (f x) 

-- Naturality axiom

mutual
  inj₂-iterD' : ∀ {A B}
    → {f : A → Delay (A ⊎ B)}
    → (b : Delay B)
    → b ≈ iterD' f (mapD inj₂ b)
  inj₂-iterD' (now x) = now
  inj₂-iterD' (later x) = later (∞inj₂-iterD' (force x))  

  ∞inj₂-iterD' : ∀ {A B}
    → {f : A → Delay (A ⊎ B)}
    → (b : Delay B)
    → b ∞≈ iterD' f (mapD inj₂ b)
  force (∞inj₂-iterD' b) = inj₂-iterD' b

mutual
  naturality' : ∀ {A B C} (g : B → Delay C) (f : A → Delay (A ⊎ B))
    → (x : Delay (A ⊎ B))
    → bindD g (iterD' f x) ≈
      iterD' ((bindD [ (λ z → now (inj₁ z)) , mapD inj₂ ∘ g ]′) ∘ f)
             (bindD [ (λ z → now (inj₁ z)) , mapD inj₂ ∘ g ]′ x)
  naturality' g f (now (inj₁ x)) = later (∞naturality' g f (f x))
  naturality' g f (now (inj₂ x)) = inj₂-iterD' (g x)
  naturality' g f (later x) = later (∞naturality' g f (force x))
  
  ∞naturality' : ∀ {A B C} (g : B → Delay C) (f : A → Delay (A ⊎ B))
    → (x : Delay (A ⊎ B))
    → bindD g (iterD' f x) ∞≈
      iterD' ((bindD [ (λ z → now (inj₁ z)) , mapD inj₂ ∘ g ]′) ∘ f)
             (bindD [ (λ z → now (inj₁ z)) , mapD inj₂ ∘ g ]′ x)
  force (∞naturality' g f x) = naturality' g f x
  
naturality : ∀ {A B C} (g : B → Delay C) (f : A → Delay (A ⊎ B))
  → g ∙ (iterD f) ∼ iterD ((bindD [ (λ z → now (inj₁ z)) , mapD inj₂ ∘ g ]′) ∘ f)
naturality g f x = naturality' g f (f x)

-- Codiagonality axiom

mutual
  codiagonal' : ∀{A B} (g : A → Delay (A ⊎ (A ⊎ B))) (x : Delay (A ⊎ (A ⊎ B)))
    → iterD' (mapD [ inj₁ , id ]′ ∘ g) (mapD [ inj₁ , id ]′ x) ≈
      iterD' (iterD g) (iterD' g x)
  codiagonal' g (now (inj₁ x)) = later (∞codiagonal' g (g x))
  codiagonal' g (now (inj₂ (inj₁ x))) = later (∞codiagonal' g (g x))
  codiagonal' g (now (inj₂ (inj₂ x))) = refl≈
  codiagonal' g (later x) = later (∞codiagonal' g (force x))

  ∞codiagonal' : ∀{A B} (g : A → Delay (A ⊎ (A ⊎ B))) (x : Delay (A ⊎ (A ⊎ B)))
    → iterD' (mapD [ inj₁ , id ]′ ∘ g) (mapD [ inj₁ , id ]′ x) ∞≈
      iterD' (iterD g) (iterD' g x)
  force (∞codiagonal' f x) = codiagonal' f x

codiagonal : ∀ {A B} (g : A → Delay (A ⊎ (A ⊎ B))) → iterD (mapD [ inj₁ , id ]′ ∘ g) ∼ iterD (iterD g)
codiagonal g x = codiagonal' g (g x)

-- Uniformity axiom

uniformity-Orb₁ : ∀ {A B C}
  → (f : A → Delay (A ⊎ B)) (g : C → Delay (C ⊎ B)) (h : C → A)
  → ((x : C) → mapD (map⊎ h id) (g x) ≈ f (h x))
  → (c : C) (b : B)
  → iter-Orb g c b → iter-Orb f (h c) b
uniformity-Orb₁ f g h p c b (done q) =
  done (trans≈ (sym≈ (p c)) (cong-bindD q))
uniformity-Orb₁ f g h p c b (step q r) =
  step (trans≈ (sym≈ (p c)) (cong-bindD q)) (uniformity-Orb₁ f g h p _ b r)

uniformity-Orb₂ : ∀ {A B C}
  → (f : A → Delay (A ⊎ B)) (g : C → Delay (C ⊎ B)) (h : C → A)
  → ((x : C) → mapD (map⊎ h id) (g x) ≈ f (h x))
  → (c : C) (b : B)
  → iter-Orb f (h c) b → iter-Orb g c b
uniformity-Orb₂ f g h p c b (done q) with bindD↓ (λ z → now ((map⊎ h id) z)) (g c) (trans≈ (p c) q)
uniformity-Orb₂ f g h p c b (done q) | inj₂ .b , r , now = done r
uniformity-Orb₂ f g h p c b (step q r) with bindD↓ (λ z → now ((map⊎ h id) z)) (g c) (trans≈ (p c) q)
uniformity-Orb₂ f g h p c b (step q r) | inj₁ c' , s , now = step s (uniformity-Orb₂ f g h p _ b r)

uniformity : ∀ {A B C}
  → (f : A → Delay (A ⊎ B)) (g : C → Delay (C ⊎ B)) (h : C → A)
  → mapD (map⊎ h id) ∘ g ∼ f ∘ h → iterD g ∼ iterD f ∘ h
uniformity f g h p x = ≈-equiv₂
  ((λ q → iterD-now-equiv₂ f (uniformity-Orb₁ f g h p x _ (iterD-now-equiv₁ g q))) ,
   (λ q → iterD-now-equiv₂ g (uniformity-Orb₂ f g h p x _ (iterD-now-equiv₁ f q))))

-- Dinaturality axiom

mutual
  dinaturality↓₁ : ∀ {A B C}
    → (g : A → Delay (C ⊎ B)) (h : C → Delay (A ⊎ B)) (x : Delay (C ⊎ B)) {b : B}
    → iterD' ([ h , (λ z → now (inj₂ z)) ]′ ∙ g) (bindD [ h , (λ z → now (inj₂ z)) ]′ x) ↓ b
    → bindD [ (iterD ([ g , (λ z → now (inj₂ z)) ]′ ∙ h)) , now ]′ x ↓ b
  dinaturality↓₁ g h (now (inj₁ x)) p = dinaturality↓₁' g h (h x) p
  dinaturality↓₁ g h (now (inj₂ y)) p = p
  dinaturality↓₁ g h (later x) (laterL p) = laterL (dinaturality↓₁ g h (force x) p)

  dinaturality↓₁' : ∀ {A B C}
    → (g : A → Delay (C ⊎ B)) (h : C → Delay (A ⊎ B)) (x : Delay (A ⊎ B)) {b : B}
    → iterD' ([ h , (λ z → now (inj₂ z)) ]′ ∙ g) x ↓ b
    → iterD' ([ g , (λ z → now (inj₂ z)) ]′ ∙ h) (bindD [ g , (λ z → now (inj₂ z)) ]′ x) ↓ b 
  dinaturality↓₁' g h (now (inj₁ x)) (laterL p) =
    trans≈ (sym≈ (fixpoint' ([ g , (λ z → now (inj₂ z)) ]′ ∙ h) (g x))) (dinaturality↓₁ g h (g x) p)
  dinaturality↓₁' g h (now (inj₂ y)) p = p
  dinaturality↓₁' g h (later x) (laterL p) = laterL (dinaturality↓₁' g h (force x) p)

mutual
  dinaturality↓₂ : ∀ {A B C}
    → (g : A → Delay (C ⊎ B)) (h : C → Delay (A ⊎ B)) (x : Delay (C ⊎ B)) {b : B}
    → iterD' ([ g , (λ z → now (inj₂ z)) ]′ ∙ h) x ↓ b
    → iterD' ([ h , (λ z → now (inj₂ z)) ]′ ∙ g) (bindD [ h , (λ z → now (inj₂ z)) ]′ x) ↓ b
  dinaturality↓₂ g h (now (inj₁ x)) (laterL p) = dinaturality↓₂' g h (h x) p
  dinaturality↓₂ g h (now (inj₂ y)) p = p
  dinaturality↓₂ g h (later x) (laterL p) = laterL (dinaturality↓₂ g h (force x) p)

  dinaturality↓₂' : ∀ {A B C}
    → (g : A → Delay (C ⊎ B)) (h : C → Delay (A ⊎ B)) (x : Delay (A ⊎ B)) {b : B}
    → iterD' ([ g , (λ z → now (inj₂ z)) ]′ ∙ h) (bindD [ g , (λ z → now (inj₂ z)) ]′ x) ↓ b
    → iterD' ([ h , (λ z → now (inj₂ z)) ]′ ∙ g) x ↓ b
  dinaturality↓₂' g h (now (inj₁ x)) p = laterL (dinaturality↓₂ g h (g x) p)
  dinaturality↓₂' g h (now (inj₂ y)) p = p
  dinaturality↓₂' g h (later x) (laterL p) = laterL (dinaturality↓₂' g h (force x) p)
  
dinatural : ∀ {A B C}
  → (g : A → Delay (C ⊎ B)) (h : C → Delay (A ⊎ B)) 
  → iterD ([ h , (λ z → now (inj₂ z)) ]′ ∙ g) ∼
    [ (iterD ([ g , (λ z → now (inj₂ z)) ]′ ∙ h)) , now ]′ ∙ g
dinatural g h x = ≈-equiv₂
  (dinaturality↓₁ g h (g x) ,
   λ p → dinaturality↓₂ g h (g x) (trans≈ (sym≈ (fixpoint' ([ g , (λ z → now (inj₂ z)) ]′ ∙ h) (g x))) p)) 

-- Bekic identity


mutual
  bekic↓₁₁' : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → bindD [ iterD ([ (iterD (mapD α⊎ ∘ f)) , now ]′ ∙ (mapD α⊎ ∘ g)) , now ]′ (iterD' (mapD α⊎ ∘ f)  (mapD α⊎ x)) ↓ c
  bekic↓₁₁' f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₁₁' f g (f x) p)
  bekic↓₁₁' f g (now (inj₁ (inj₂ y))) (laterL p) = bekic↓₁₂ f g (g y) p
  bekic↓₁₁' f g (now (inj₂ y)) p = p
  bekic↓₁₁' f g (later x) (laterL p) = laterL (bekic↓₁₁' f g (force x) p)

  bekic↓₁₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → iterD' ([ iterD (mapD α⊎ ∘ f) , now ]′ ∙ (mapD α⊎ ∘ g)) (iterD' (mapD α⊎ ∘ f) (mapD α⊎ x)) ↓ c
  bekic↓₁₁ f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₁₁ f g (f x) p)
  bekic↓₁₁ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₁₂ f g (g y) p)
  bekic↓₁₁ f g (now (inj₂ y)) p = p
  bekic↓₁₁ f g (later x) (laterL p) = laterL (bekic↓₁₁ f g (force x) p)
  
  bekic↓₁₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' [ f , g ]′ x ↓ c
    → iterD' ([ iterD (mapD α⊎ ∘ f) , now ]′ ∙ (mapD α⊎ ∘ g)) (bindD [ iterD (mapD α⊎ ∘ f) , now ]′ (mapD α⊎ x)) ↓ c
  bekic↓₁₂ f g (now (inj₁ (inj₁ x))) (laterL p) = bekic↓₁₁ f g (f x) p
  bekic↓₁₂ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₁₂ f g (g y) p)
  bekic↓₁₂ f g (now (inj₂ y)) p = p
  bekic↓₁₂ f g (later x) (laterL p) = laterL (bekic↓₁₂ f g (force x) p)

bekic↓₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : A ⊎ B) {c : C}
  → iterD [ f , g ]′ x ↓ c
  → bindD [ iterD ([ (iterD (mapD α⊎ ∘ f)) , now ]′ ∙ (mapD α⊎ ∘ g)) , now ]′ ([ iterD (mapD α⊎ ∘ f) , (λ z → now (inj₁ z)) ]′ x) ↓ c
bekic↓₁ f g (inj₁ x) p = bekic↓₁₁' f g (f x) p
bekic↓₁ f g (inj₂ y) p = bekic↓₁₂ f g (g y) p  

mutual
  bekic↓₂₁' : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → bindD [ iterD ([ (iterD (mapD α⊎ ∘ f)) , now ]′ ∙ (mapD α⊎ ∘ g)) , now ]′ (iterD' (mapD α⊎ ∘ f)  (mapD α⊎ x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₁' f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₂₁' f g (f x) p)
  bekic↓₂₁' f g (now (inj₁ (inj₂ y))) p = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₁' f g (now (inj₂ y)) p = p
  bekic↓₂₁' f g (later x) (laterL p) = laterL (bekic↓₂₁' f g (force x) p)

  bekic↓₂₁ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' ([ iterD (mapD α⊎ ∘ f) , now ]′ ∙ (mapD α⊎ ∘ g)) (iterD' (mapD α⊎ ∘ f) (mapD α⊎ x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₁ f g (now (inj₁ (inj₁ x))) (laterL p) = laterL (bekic↓₂₁ f g (f x) p)
  bekic↓₂₁ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₁ f g (now (inj₂ y)) p = p
  bekic↓₂₁ f g (later x) (laterL p) = laterL (bekic↓₂₁ f g (force x) p)

  bekic↓₂₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : Delay ((A ⊎ B) ⊎ C)) {c : C}
    → iterD' ([ iterD (mapD α⊎ ∘ f) , now ]′ ∙ (mapD α⊎ ∘ g)) (bindD [ iterD (mapD α⊎ ∘ f) , now ]′ (mapD α⊎ x)) ↓ c
    → iterD' [ f , g ]′ x ↓ c
  bekic↓₂₂ f g (now (inj₁ (inj₁ x))) p = laterL (bekic↓₂₁ f g (f x) p) 
  bekic↓₂₂ f g (now (inj₁ (inj₂ y))) (laterL p) = laterL (bekic↓₂₂ f g (g y) p)
  bekic↓₂₂ f g (now (inj₂ y)) p = p
  bekic↓₂₂ f g (later x) (laterL p) = laterL (bekic↓₂₂ f g (force x) p)

bekic↓₂ : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C)) (x : A ⊎ B) {c : C}
  → bindD [ iterD ([ (iterD (mapD α⊎ ∘ f)) , now ]′ ∙ (mapD α⊎ ∘ g)) , now ]′ ([ iterD (mapD α⊎ ∘ f) , (λ z → now (inj₁ z)) ]′ x) ↓ c
  → iterD [ f , g ]′ x ↓ c
bekic↓₂ f g (inj₁ x) p = bekic↓₂₁' f g (f x) p
bekic↓₂ f g (inj₂ y) p = bekic↓₂₂ f g (g y) p

bekic : ∀ {A B C} (f : A → Delay ((A ⊎ B) ⊎ C)) (g : B → Delay ((A ⊎ B) ⊎ C))
  → iterD [ f , g ]′ ∼
    [ iterD ([ (iterD (mapD α⊎ ∘ f)) , now ]′ ∙ (mapD α⊎ ∘ g)) , now ]′ ∙ [ iterD (mapD α⊎ ∘ f) , (λ z → now (inj₁ z)) ]′
bekic f g x = ≈-equiv₂ (bekic↓₁ f g x , bekic↓₂ f g x)  


-- Equivalence with Hasegawa's trace operator.

traceD2 : {A B U : Set} → (U ⊎ A → Delay (U ⊎ B)) → A → Delay B
traceD2 f = iterD (mapD (map⊎ inj₁ id) ∘ f) ∘ inj₂

mutual
  iterD-eq : {A B U : Set} (f : U ⊎ A → Delay (U ⊎ B))
    → (x : Delay (U ⊎ B))
    → iterD' (f L) x ≈ iterD' (mapD (map⊎ inj₁ id) ∘ f) (mapD (map⊎ inj₁ id) x)
  iterD-eq f (now (inj₁ x)) = later (∞iterD-eq f ((f L) x))
  iterD-eq f (now (inj₂ y)) = now
  iterD-eq f (later x) = later (∞iterD-eq f (force x))  

  ∞iterD-eq : {A B U : Set} (f : U ⊎ A → Delay (U ⊎ B))
    → (x : Delay (U ⊎ B))
    → iterD' (f L) x ∞≈ iterD' (mapD (map⊎ inj₁ id) ∘ f) (mapD (map⊎ inj₁ id) x)
  force (∞iterD-eq f x) = iterD-eq f x

traceD-eq : {A B U : Set} (f : U ⊎ A → Delay (U ⊎ B))
  → traceD f ∼ traceD2 f
traceD-eq f x = trans≈ (fixpoint' (f L) ((f R) x)) (iterD-eq f ((f R) x) )  

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
  → f ∼ ((λ x → now (inj₂ x)) ∙ traceD f) ∙ (now ∘ λ⊎)
vanishingI-traceD {f = f} (inj₂ y) =
  trans≈ (sym≈ (M2 ((f R) y)))
    (trans≈ (cong-app-bindD ((f R) y) (λ { (inj₂ x) → refl≈ }))
      (sym≈ (M3 ((f R) y))))

vanishingII-traceD : ∀ {A B C D} {f : (A ⊎ B) ⊎ C → Delay ((A ⊎ B) ⊎ D)}
    → traceD f ∼ traceD (traceD (mapD α⊎ ∘ f ∘ α⊎-1))
vanishingII-traceD {A}{B}{C}{D} {f = f} =
  proof
    traceD f
  ∼〈 refl∼ 〉
    [ iterD (f L) , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (copair∼ (cong-iterD (λ { (inj₁ x) → refl≈ ; (inj₂ y) → refl≈ })) refl∼) refl∼ 〉
    [ iterD [ f L L , f L R ]′ , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (copair∼ (bekic (f L L) (f L R)) refl∼) refl∼ 〉
    [ [ iterD ([ (iterD (mapD α⊎ ∘ (f L L))) , now ]′ ∙ (mapD α⊎ ∘ (f L R))) , now ]′ ∙ [ iterD (mapD α⊎ ∘ (f L L)) , (λ z → now (inj₁ z)) ]′ , now ]′ ∙ (f R)
  ∼〈 cong∙ {f = f R} (λ { (inj₁ (inj₁ y)) → refl≈ ; (inj₁ (inj₂ y)) → refl≈ ; (inj₂ y) → refl≈ }) refl∼ 〉
    (([ iterD ([ iterD (mapD α⊎ ∘ (f L L)) , now ]′ ∙ (mapD α⊎ ∘ (f L R))) , now ]′ ∙ [ iterD (mapD α⊎ ∘ (f L L)) , now ]′) ∘ α⊎) ∙ (f R)
  ∼〈 sym∼ (assoc∙ {f = f R}) 〉
    ([ iterD ([ iterD (mapD α⊎ ∘ (f L L)) , now ]′ ∙ (mapD α⊎ ∘ (f L R))) , now ]′ ∙ [ iterD (mapD α⊎ ∘ (f L L)) , now ]′) ∙ (mapD α⊎ ∘ (f R))
  ∼〈 sym∼ (assoc∙ {f = mapD α⊎ ∘ (f R)}) 〉
    [ iterD ([ iterD (mapD α⊎ ∘ (f L L)) , now ]′ ∙ (mapD α⊎ ∘ (f L R))) , now ]′ ∙ ([ iterD (mapD α⊎ ∘ (f L L)) , now ]′ ∙ (mapD α⊎ ∘ (f R)))
  ∼〈 refl∼ 〉
    [ iterD ((traceD (mapD α⊎ ∘ f ∘ α⊎-1)) L) , now ]′ ∙ ((traceD (mapD α⊎ ∘ f ∘ α⊎-1)) R)
  ∼〈 refl∼ 〉
    traceD (traceD (mapD α⊎ ∘ f ∘ α⊎-1))
  qed
  where
    open Eq∼

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
  ∼〈 cong∙ {f = g R} (copair∼ (fixpoint ((g L) ∙ f)) refl∼) refl∼ 〉
    [ iterD ((g L) ∙ f) , now ]′ ∙ (g R)
  ∼〈 cong∙ {f = g R} (copair∼ (cong-iterD (sym∼ (M3 ∘ f))) refl∼) refl∼ 〉
    [ iterD (g ∙ (mapD inj₁ ∘ f)) , now ]′ ∙ (g R)
  ∼〈 refl∼ 〉
    traceD (g ∙ [ mapD inj₁ ∘ f , (λ z → now (inj₂ z)) ]′)
  qed
  where
    open Eq∼

superposing-traceD : {A B C D : Set} {f : A ⊎ B → Delay (A ⊎ C)}
  → traceD (mapD α⊎ ∘ map⊎D f now ∘ α⊎-1) ∼ map⊎D (traceD f) (now {A = D})
superposing-traceD {A}{B}{C}{D}{f = f} (inj₁ x) =
  trans≈ (M3 (bindD (λ x₁ → now (inj₁ x₁)) (f (inj₂ x))))
    (trans≈ (M3 ((f R) x))
      (trans≈ (cong-app-bindD ((f R) x)
                (λ { (inj₁ y) → trans≈ (cong-iterD''  (λ a → M3 ((f L) a)) (M3 ((f L) y))) (lem ((f L) y))
                   ; (inj₂ z) → now }))
        (sym≈ (M3 ((f R) x)))))
  where
    mutual
      lem : (z : Delay (A ⊎ C))
        → iterD' (mapD (α⊎ L) ∘ (f L)) (mapD (α⊎ L) z) ≈ mapD inj₁ (iterD' (f L) z)
      lem (now (inj₁ y)) = later (∞lem (f (inj₁ y)))
      lem (now (inj₂ y)) = now
      lem (later y) = later (∞lem (force y))

      ∞lem : (z : Delay (A ⊎ C))
        → iterD' (mapD (α⊎ L) ∘ (f L)) (mapD (α⊎ L) z) ∞≈ mapD inj₁ (iterD' (f L) z)
      force (∞lem z) = lem z

superposing-traceD {f = f} (inj₂ y) = now  
