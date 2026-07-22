module Cubical.Categories.Displayed.Univalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Instances.TotalCategory
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
