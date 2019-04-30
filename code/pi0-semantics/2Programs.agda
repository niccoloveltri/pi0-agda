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

sem-⟺ : ∀ {n} (F : Fin n → Set) {A B : Ty n} {f g : A ⟷ B}
  → f ⟺ g → sem-⟷ F f ≃₂ sem-⟷ F g
sem-⟺ F id⟺ = refl∼
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
sem-⟺ F (inve {f = f}) =
  trans∼ (cong∙ {f = proj₁ (sem-⟷ F f)} (cong∙ refl∼ (dagger-eq F f)) refl∼)
    (pinv-eq (is-partial-inv.β (proj₂ (sem-⟷ F f))))
sem-⟺ F (invu {f = f}{g}) =
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

{-






-- Interpretation of Π₀-program equivalences into the Kleisli category of Delay

sem-⊕₂ : ∀ {A B C D} {f g : A ≃₁ B} {f' g' : C ≃₁ D}
  → f ≃₂ g → f' ≃₂ g'
  → (f sem-⊕ f') ≃₂ (g sem-⊕ g')
sem-⊕₂ p q (inj₁ x) = cong-bindD (p x)
sem-⊕₂ p q (inj₂ y) = cong-bindD (q y)


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
-}
