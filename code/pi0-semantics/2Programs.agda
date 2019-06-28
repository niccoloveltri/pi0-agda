{-# OPTIONS --without-K #-}

module pi0-semantics.2Programs where

open import Data.Empty
open import Data.Sum renaming (map to map⊎; swap to swap⊎)
open import Data.Unit
open import Data.Product renaming (map to map×; swap to swap×)
open import Relation.Binary.PropositionalEquality hiding (naturality)
open import Function
open import Data.Nat
open import Data.Fin hiding (fold)

open import Utilities
open import pi0-syntax.Types
open import pi0-syntax.1Programs
open import pi0-syntax.2Programs
open import pi0-semantics.Types
open import pi0-semantics.1Programs

open import delay.Delay
open import delay.Monad
open import delay.Elgot
open import delay.PartialInv
open import delay.Structure

-- Interpretation of the syntactic dagger is equivalent to the semantic dagger

dagger-eq : ∀ {n} (F : Fin n → Set) {A B} (f : A ⟷ B)
  → sem-⟷ F (dagger f) ≃₂ sem-dagger (sem-⟷ F f)
dagger-eq F id⟷ = refl∼
dagger-eq F λ⊕ = refl∼
dagger-eq F λ⊕-1 = refl∼
dagger-eq F α⊕ = refl∼
dagger-eq F α⊕-1 = refl∼
dagger-eq F s⊕ = refl∼
dagger-eq F λ⊗ = refl∼
dagger-eq F λ⊗-1 = refl∼
dagger-eq F α⊗ = refl∼
dagger-eq F α⊗-1 = refl∼
dagger-eq F s⊗ = refl∼
dagger-eq F κL = refl∼
dagger-eq F κL-1 = refl∼
dagger-eq F δR = refl∼
dagger-eq F δR-1 = refl∼
dagger-eq F (f ⊙ f₁) = cong∙ (dagger-eq F f₁) (dagger-eq F f)
dagger-eq F (f ⊕ f₁) (inj₁ x) = cong-bindD (dagger-eq F f x)
dagger-eq F (f ⊕ f₁) (inj₂ y) = cong-bindD (dagger-eq F f₁ y)
dagger-eq F (f ⊗ f₁) (x , y) = cong-θ (dagger-eq F f x) (dagger-eq F f₁ y)
dagger-eq F fold = refl∼
dagger-eq F unfold = refl∼
dagger-eq F (trace f) x =
  cong-bindD₂ (copair∼ (cong-iterD (λ y → dagger-eq F f (inj₁ y))) refl∼)
              (dagger-eq F f (inj₂ x))

-- Interpretation of term equivalences

sem-existsPIso : ∀ {n} (F : Fin n → Set) {A B : Ty n} {f : A ⟷ B} → ((sem-⟷ F f ⊙≃₁ sem-⟷ F (dagger f)) ⊙≃₁ sem-⟷ F f) ≃₂ sem-⟷ F f
sem-existsPIso F {f = f} = trans∼ (cong∙ {f = proj₁ (sem-⟷ F f)} (cong∙ refl∼ (dagger-eq F f)) refl∼)
    (pinv-eq (is-partial-inv.β (proj₂ (sem-⟷ F f))))


sem-⟺ : ∀ {n} (F : Fin n → Set) {A B : Ty n} {f g : A ⟷ B}
  → f ⟺ g → sem-⟷ F f ≃₂ sem-⟷ F g
sem-⟺ F id⟺ = refl∼
sem-⟺ F (sym⟺ p) = sym∼ (sem-⟺ F p)
sem-⟺ F (trans⟺ p p') = trans∼ (sem-⟺ F p') (sem-⟺ F p)
sem-⟺ F (p ⊙ p') = cong∙ (sem-⟺ F p) (sem-⟺ F p')
sem-⟺ F (p ⊕ p') =
  copair∼ (cong∙ refl∼ (sem-⟺ F p)) (cong∙ refl∼ (sem-⟺ F p'))
sem-⟺ F (_⊗_ {f = f}{g}{f'}{g'} p p') (a , c) =
  trans≈ (M3 (proj₁ (sem-⟷ F f') c))
    (trans≈ (cong∙ (λ _ → cong-bindD (sem-⟺ F p a)) (sem-⟺ F p') c)
      (sym≈ (M3 (proj₁ (sem-⟷ F g') c))))
sem-⟺ F lid a = M2 _
sem-⟺ F rid = refl∼
sem-⟺ F (ass {f = f}) = assoc∙ {f = proj₁ (sem-⟷ F f)}
sem-⟺ F (uniquePIso {f = f}{g}) =
  trans∼ (cong∙ (cong∙ {f = proj₁ (sem-⟷ F g)} (cong∙ {g = proj₁ (sem-⟷ F f)} refl∼ (dagger-eq F f)) refl∼) (dagger-eq F g))
    (trans∼ (pinv-u (is-partial-inv.α (proj₂ (sem-⟷ F f))) (is-partial-inv.α (proj₂ (sem-⟷ F g))))
      (sym∼ (cong∙ (cong∙ {f = proj₁ (sem-⟷ F f)} (cong∙ {g = proj₁ (sem-⟷ F g)} refl∼ (dagger-eq F g)) refl∼) (dagger-eq F f))))
sem-⟺ F fun⊕id (inj₁ a) = now
sem-⟺ F fun⊕id (inj₂ b) = now
sem-⟺ F (fun⊕⊙ {f = f}) (inj₁ a) =
  trans≈ (M3 (proj₁ (sem-⟷ F f) a)) (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
sem-⟺ F (fun⊕⊙ {h = h}) (inj₂ d) = 
  trans≈ (M3 (proj₁ (sem-⟷ F h) d)) (sym≈ (M3 (proj₁ (sem-⟷ F h) d)))
sem-⟺ F fun⊗id = refl∼
sem-⟺ F (fun⊗⊙ {f = f}{h = h}) =
  fun∙×D {f = proj₁ (sem-⟷ F f)}{h = proj₁ (sem-⟷ F h)}
sem-⟺ F (nλ⊕ {f = f}) (inj₂ a) =
  trans≈ (sym≈ (M2 _)) (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
sem-⟺ F (nα⊕ {f = f}) (inj₁ (inj₁ a)) =
  trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
         (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F f) a))))
sem-⟺ F (nα⊕ {g = g}) (inj₁ (inj₂ c)) = 
  trans≈ (M3 (proj₁ (sem-⟷ F g) c))
    (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F g) c)))
            (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F g) c)))))
sem-⟺ F (nα⊕ {h = h}) (inj₂ e) =
  trans≈ (M3 (proj₁ (sem-⟷ F h) e)) (sym≈ (M3 (proj₁ (sem-⟷ F h) e)))
sem-⟺ F (ns⊕ {g = g}) (inj₁ c) = sym≈ (M3 (proj₁ (sem-⟷ F g) c))
sem-⟺ F (ns⊕ {f = f}) (inj₂ a) = sym≈ (M3 (proj₁ (sem-⟷ F f) a))
sem-⟺ F λ⊕Iso x = now
sem-⟺ F λ⊕-1Iso (inj₂ y) = now
sem-⟺ F α⊕Iso (inj₁ x) = now
sem-⟺ F α⊕Iso (inj₂ (inj₁ x)) = now
sem-⟺ F α⊕Iso (inj₂ (inj₂ y)) = now
sem-⟺ F α⊕-1Iso (inj₁ (inj₁ x)) = now
sem-⟺ F α⊕-1Iso (inj₁ (inj₂ y)) = now
sem-⟺ F α⊕-1Iso (inj₂ y) = now
sem-⟺ F s⊕Iso (inj₁ x) = now
sem-⟺ F s⊕Iso (inj₂ y) = now
sem-⟺ F (nλ⊗ {f = f}) (tt , a) =
  trans≈ (sym≈ (M2 _))
    (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F f) a))) (cong-bindD (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))))
sem-⟺ F (nα⊗ {f = f}{g}{h}) ((a , c) , e) =
  trans≈ (cong-bindD (cong-bindD (M3 (proj₁ (sem-⟷ F h) e))))
    (trans≈ (cong-bindD (M3 (proj₁ (sem-⟷ F h) e)))
      (trans≈ (M3 (proj₁ (sem-⟷ F h) e))
        (trans≈ (cong-app-bindD (proj₁ (sem-⟷ F h) e)
                  (λ x → trans≈ (cong-bindD (M3 (proj₁ (sem-⟷ F g) c)))
                           (trans≈ (M3 (proj₁ (sem-⟷ F g) c))
                             (trans≈ (cong-app-bindD (proj₁ (sem-⟷ F g) c)
                                       (λ y → trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
                                                (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F f) a))))))
                               (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F g) c)))
                                 (trans≈ (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F g) c))))
                                   (sym≈ (cong-bindD (cong-bindD (M3 (proj₁ (sem-⟷ F g) c)))))))))))
          (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F h) e))) (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F h) e))))))))
sem-⟺ F (ns⊗ {f = f}{g}) (c , a) =
  trans≈ (θ-eq (proj₁ (sem-⟷ F f) a , proj₁ (sem-⟷ F g) c))
    (trans≈ (M3 (proj₁ (sem-⟷ F f) a))
      (trans≈ (cong-app-bindD (proj₁ (sem-⟷ F f) a) (λ _ → sym≈ (M3 (proj₁ (sem-⟷ F g) c))))
        (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
          (sym≈ (cong-bindD (M3 (proj₁ (sem-⟷ F f) a)))))))
sem-⟺ F λ⊗Iso x = now
sem-⟺ F λ⊗-1Iso x = now
sem-⟺ F α⊗Iso x = now
sem-⟺ F α⊗-1Iso x = now
sem-⟺ F s⊗Iso x = now
sem-⟺ F nκL (() , _)
sem-⟺ F (nδR {f = f}{h = h}) (inj₁ a , e) =
  trans≈ (M3 (bindD (λ x → now (proj₁ (sem-⟷ F f) a , x)) (proj₁ (sem-⟷ F h) e)))
    (trans≈ (M3 (proj₁ (sem-⟷ F h) e))
      (trans≈ (cong-app-bindD (proj₁ (sem-⟷ F h) e)
                (λ x → trans≈ (M3 (proj₁ (sem-⟷ F f) a))
                         (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F f) a)))
                           (sym≈ (M3 (bindD (λ z → now (inj₁ z)) (proj₁ (sem-⟷ F f) a)))))))
        (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F h) e)))
          (cong-bindD (sym≈ (M3 (proj₁ (sem-⟷ F h) e)))))))
sem-⟺ F (nδR {g = g}{h}) (inj₂ c , e) = --{!!}
  trans≈ (M3 (bindD (λ x → now (proj₁ (sem-⟷ F g) c , x)) (proj₁ (sem-⟷ F h) e)))
    (trans≈ (M3 (proj₁ (sem-⟷ F h) e))
      (trans≈ (cong-app-bindD (proj₁ (sem-⟷ F h) e)
                (λ x → trans≈ (M3 (proj₁ (sem-⟷ F g) c))
                         (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F g) c)))
                           (sym≈ (M3 (bindD (λ z → now (inj₂ z)) (proj₁ (sem-⟷ F g) c)))))))
        (trans≈ (sym≈ (M3 (proj₁ (sem-⟷ F h) e)))
          (cong-bindD (sym≈ (M3 (proj₁ (sem-⟷ F h) e)))))))
sem-⟺ F κLIso ()
sem-⟺ F κL-1Iso ()
sem-⟺ F δRIso (inj₁ x) = now
sem-⟺ F δRIso (inj₂ y) = now
sem-⟺ F δR-1Iso (inj₁ x , c) = now
sem-⟺ F δR-1Iso (inj₂ y , c) = now
sem-⟺ F ραλ⊕ (inj₁ (inj₁ a)) = now
sem-⟺ F ραλ⊕ (inj₂ b) = now
sem-⟺ F ααα⊕ (inj₁ (inj₁ (inj₁ x))) = now
sem-⟺ F ααα⊕ (inj₁ (inj₁ (inj₂ y))) = now
sem-⟺ F ααα⊕ (inj₁ (inj₂ y)) = now
sem-⟺ F ααα⊕ (inj₂ y) = now
sem-⟺ F ρsλ⊕ (inj₁ b) = now
sem-⟺ F ss⊕ (inj₁ a) = now
sem-⟺ F ss⊕ (inj₂ b) = now
sem-⟺ F sα⊕ (inj₁ (inj₁ x)) = now
sem-⟺ F sα⊕ (inj₁ (inj₂ y)) = now
sem-⟺ F sα⊕ (inj₂ y) = now
sem-⟺ F ραλ⊗ = refl∼
sem-⟺ F ααα⊗ = refl∼
sem-⟺ F ρsλ⊗ = refl∼
sem-⟺ F ss⊗ = refl∼
sem-⟺ F sα⊗ = refl∼
sem-⟺ F I (a , inj₁ b) = now
sem-⟺ F I (a , inj₂ c) = now
sem-⟺ F II (inj₁ a , c) = now
sem-⟺ F II (inj₂ b , c) = now
sem-⟺ F III (inj₁ a , c) = now
sem-⟺ F III (inj₂ b , c) = now
sem-⟺ F IV (inj₁ a , d) = now
sem-⟺ F IV (inj₂ (inj₁ b) , d) = now
sem-⟺ F IV (inj₂ (inj₂ c) , d) = now
sem-⟺ F V (a , inj₁ b) = now
sem-⟺ F V (a , inj₂ (inj₁ c)) = now
sem-⟺ F V (a , inj₂ (inj₂ d)) = now
sem-⟺ F VI (a , b , inj₁ c) = now
sem-⟺ F VI (a , b , inj₂ d) = now
sem-⟺ F VII (inj₁ a , c , d) = now
sem-⟺ F VII (inj₂ b , c , d) = now
sem-⟺ F VIII (a , inj₁ b , d) = now
sem-⟺ F VIII (a , inj₂ c , d) = now
sem-⟺ F IX (inj₁ a , inj₁ c) = now
sem-⟺ F IX (inj₁ a , inj₂ d) = now
sem-⟺ F IX (inj₂ b , inj₁ c) = now
sem-⟺ F IX (inj₂ b , inj₂ d) = now
sem-⟺ F X (() , _)
sem-⟺ F XI (() , _)
sem-⟺ F XII (_ , ())
sem-⟺ F XIII (() , _)
sem-⟺ F XIV (_ , ())
sem-⟺ F XV (_ , ())
sem-⟺ F XVI (() , _)
sem-⟺ F XVII (_ , () , _)
sem-⟺ F XVIII (_ , _ , ())
sem-⟺ F XIX (a , inj₂ b) = now
sem-⟺ F XX (inj₂ a , b) = now
sem-⟺ F XXI (a , inj₁ b) = now
sem-⟺ F XXII (inj₁ a , b) = now
sem-⟺ F XXIII (tt , inj₁ a) = now
sem-⟺ F XXIII (tt , inj₂ b) = now
sem-⟺ F XXIV (inj₁ a , tt) = now
sem-⟺ F XXIV (inj₂ b , tt) = now
sem-⟺ F (naturalityL {f = f}{g}) = naturalityL-traceD {f = proj₁ (sem-⟷ F f)} {proj₁ (sem-⟷ F g)}
sem-⟺ F (naturalityR {f = f}) = naturalityR-traceD {f = proj₁ (sem-⟷ F f)}
sem-⟺ F (dinaturality {f = f}{g}) = dinaturality-traceD {f = proj₁ (sem-⟷ F f)} {proj₁ (sem-⟷ F g)}
sem-⟺ F (superposing {f = f}) = superposing-traceD {f = proj₁ (sem-⟷ F f)}
sem-⟺ F (vanishingI {f = f}) = vanishingI-traceD {f = proj₁ (sem-⟷ F f)}
sem-⟺ F (vanishingII {f = f}) = vanishingII-traceD {f = proj₁ (sem-⟷ F f)}
sem-⟺ F yanking = refl∼
sem-⟺ F (tracePIso {f = f}) = sem-existsPIso F {f = trace f} 
sem-⟺ F foldIso (sup x) = now
sem-⟺ F unfoldIso = refl∼

