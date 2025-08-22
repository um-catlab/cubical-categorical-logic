module Cubical.Categories.Displayed.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'}(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module ∫Cᴰ = Category (∫C Cᴰ)
  path∫ToIsoᴰ : ∀ {x xᴰ y yᴰ}
    → (p : Path ∫Cᴰ.ob (x , xᴰ) (y , yᴰ))
    → CatIsoᴰ Cᴰ (pathToIso (cong fst p)) xᴰ yᴰ
  path∫ToIsoᴰ {xᴰ = xᴰ} = J (λ (y , yᴰ) p → CatIsoᴰ Cᴰ (pathToIso (cong fst p)) xᴰ yᴰ) $
    subst⁻ (λ f → CatIsoᴰ Cᴰ f xᴰ xᴰ) pathToIso-refl (idᴰCatIsoᴰ Cᴰ)

  pathPToIsoᴰ : ∀ {x}{xᴰ : Cᴰ.ob[ x ] }{y}
    → (p : x ≡ y){yᴰ : Cᴰ.ob[ y ]}(pᴰ : PathP (λ i → Cᴰ.ob[ p i ]) xᴰ yᴰ)
    → CatIsoᴰ Cᴰ (pathToIso p) xᴰ yᴰ
  pathPToIsoᴰ {x}{xᴰ} = JDep (λ y p yᴰ pᴰ → CatIsoᴰ Cᴰ (pathToIso p) xᴰ yᴰ)
    (subst⁻ (λ f → CatIsoᴰ Cᴰ f xᴰ xᴰ) pathToIso-refl (idᴰCatIsoᴰ Cᴰ))

-- Univalent Displayed Categories
record isUnivalentᴰ {C : Category ℓC ℓC'}(isUnivC : isUnivalent C) (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
  open isUnivalent isUnivC
  open Categoryᴰ Cᴰ
  field
    -- TODO: port this to use HAEquivOver?
    univᴰ : ∀ {x y} (xᴰ : ob[ x ])(yᴰ : ob[ y ])
      → isEquivᴰ {P = λ x≡y → PathP (λ i → ob[ x≡y i ]) xᴰ yᴰ}
                 {Q = λ f → CatIsoᴰ Cᴰ f xᴰ yᴰ}
                 (univ x y)
                 λ p pᴰ → pathPToIsoᴰ Cᴰ p pᴰ

  univEquivᴰ : ∀ {x y}{xᴰ : ob[ x ]}{yᴰ : ob[ y ]}
    → (λ p → PathP (λ i → ob[ p i ]) xᴰ yᴰ)
        ≃[ univEquiv x y ]
      (λ f → CatIsoᴰ Cᴰ f xᴰ yᴰ)
  univEquivᴰ = (λ p pᴰ → pathPToIsoᴰ Cᴰ p pᴰ) , λ q → univᴰ _ _ q

  CatIsoᴰToPathP : ∀ {x y}{xᴰ yᴰ}{p : CatIso C x y}
    → (pᴰ : CatIsoᴰ Cᴰ p xᴰ yᴰ)
    → PathP (λ i → ob[ CatIsoToPath p i ]) xᴰ yᴰ
  CatIsoᴰToPathP {x} {y} = invEqᴰ {eq = univEquiv x y} univEquivᴰ _
