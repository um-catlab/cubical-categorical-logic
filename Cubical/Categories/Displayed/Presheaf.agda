{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓPᴰ : Level

open Category
open Functor
open Functorᴰ

-- equivalent to the data of a presheaf Pᴰ over ∫ D and a natural transformation
-- Pᴰ → P ∘ Fst
Presheafᴰ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (P : Presheaf C ℓP) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-suc ℓP))
                    (ℓ-suc ℓPᴰ))
Presheafᴰ {ℓP = ℓP} D P ℓPᴰ = Functorᴰ P (D ^opᴰ) (SETᴰ ℓP ℓPᴰ)

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ D P ℓPᴰ) where

  record UniversalElementᴰ (ue : UniversalElement C P)
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') (ℓ-max ℓP ℓPᴰ)) where
    open UniversalElementNotation ue
    open Categoryᴰ D
    field
      vertexᴰ : ob[ vertex ]
      elementᴰ : ⟨ Pᴰ .F-obᴰ vertexᴰ element ⟩
      universalᴰ : ∀ {x xᴰ} →
        isIsoOver (equivToIso (_ , (universal x)))
          Hom[_][ xᴰ , vertexᴰ ]
          (λ p → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩)
          λ f fᴰ → Pᴰ .F-homᴰ fᴰ element elementᴰ
    open isIsoOver

    introᴰ : ∀ {x xᴰ} (p : ⟨ P ⟅ x ⟆ ⟩)
        → ⟨ Pᴰ .F-obᴰ xᴰ p ⟩
        → D [ intro p ][ xᴰ , vertexᴰ ]
    introᴰ p pᴰ = universalᴰ .inv p pᴰ

    βᴰ : ∀ {x xᴰ} {p : ⟨ P ⟅ x ⟆ ⟩} {pᴰ : ⟨ Pᴰ .F-obᴰ xᴰ p ⟩}
         → PathP (λ i → ⟨ Pᴰ .F-obᴰ xᴰ (β {p = p} i) ⟩)
             (Pᴰ .F-homᴰ (introᴰ p pᴰ) element elementᴰ)
             pᴰ
    βᴰ = universalᴰ .rightInv _ _

    ηᴰ : ∀ {x xᴰ} {f : C [ x , vertex ]} {fᴰ : D [ f ][ xᴰ , vertexᴰ ]}
         → fᴰ ≡[ η {f = f} ] introᴰ _ (F-homᴰ Pᴰ fᴰ element elementᴰ)
    ηᴰ = symP (universalᴰ .leftInv _ _)


-- A vertical presheaf is a displayed presheaf over a representable
Presheafⱽ : {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
          → (c : C .ob) → (ℓPᴰ : Level)
          → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC (ℓ-suc ℓC')) ℓD) ℓD')
                        (ℓ-suc ℓPᴰ))
Presheafⱽ D c = Presheafᴰ D (YO ⟅ c ⟆)

actⱽ : {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
          → {x : C .ob} → {ℓP : Level}
  → (Pⱽ : Presheafⱽ Cᴰ x ℓP)
  → ∀ {y}{yᴰ xᴰ} {f : C [ y , x ]}
  → Cᴰ [ f ][ yᴰ , xᴰ ]
  → ⟨ Pⱽ .F-obᴰ xᴰ (C .id) ⟩
  → ⟨ Pⱽ .F-obᴰ yᴰ f ⟩
actⱽ {C = C} Pⱽ fᴰ pⱽ =
  subst (λ f → ⟨ Pⱽ .F-obᴰ _ f ⟩) (C .⋆IdR _) (Pⱽ .F-homᴰ  fᴰ _ pⱽ)

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD')
         (x : C .ob) (Pᴰ : Presheafⱽ D x ℓPᴰ) where
  record UniversalElementⱽ
    : Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD') ℓPᴰ) where
    open Categoryᴰ D
    field
      vertexⱽ : ob[ x ]
      elementⱽ : ⟨ Pᴰ .F-obᴰ vertexⱽ (C .id) ⟩
      universalⱽ : ∀ {y yᴰ}{f : C [ y , x ]} →
        isIso λ (fᴰ : D [ f ][ yᴰ , vertexⱽ ]) → actⱽ Pᴰ fᴰ elementⱽ

    introⱽ : ∀ {y yᴰ} (f : C [ y , x ])
      → ⟨ Pᴰ .F-obᴰ yᴰ f ⟩
      → D [ f ][ yᴰ , vertexⱽ ]
    introⱽ f = universalⱽ .fst

    βⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {pᴰ : ⟨ Pᴰ .F-obᴰ yᴰ f ⟩}
      → actⱽ Pᴰ (introⱽ f pᴰ) elementⱽ ≡ pᴰ
    βⱽ = universalⱽ .snd .fst _

    ηⱽ : ∀ {y yᴰ} {f : C [ y , x ]} {fᴰ : D [ f ][ yᴰ , vertexⱽ ]}
      → fᴰ ≡ introⱽ f (actⱽ Pᴰ fᴰ elementⱽ)
    ηⱽ = sym (universalⱽ .snd .snd _)
