-- | Structure displayed over a category.
module Cubical.Categories.LocallySmall.Displayed.Instances.StructureOver.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.HLevels

record StructureOver
  (C : Category Cob CHom-ℓ)
  (ob[_] : Cob → Typeω)
  (Hom-ℓᴰ : ∀ x y (xᴰ : ob[ x ])(yᵈ : ob[ y ]) → Level) : Typeω where
  open CategoryNotation C
  field
    Hom[_][_,_] : ∀ {x y}(f : Hom[ x , y ])(xᴰ : ob[ x ])(yᴰ : ob[ y ])
      → Type (Hom-ℓᴰ _ _ xᴰ yᴰ)
    idᴰ : ∀ {x} {xᴰ : ob[ x ]} → Hom[ id ][ xᴰ , xᴰ ]
    _⋆ᴰ_ : ∀ {x y z} {f : Hom[ x , y ]} {g : Hom[ y , z ]} {xᴰ yᴰ zᴰ}
      → Hom[ f ][ xᴰ , yᴰ ] → Hom[ g ][ yᴰ , zᴰ ]
      → Hom[ f ⋆ g ][ xᴰ , zᴰ ]
    isPropHomᴰ : ∀ {x y} {f : Hom[ x , y ]} {xᴰ yᴰ}
      → isProp Hom[ f ][ xᴰ , yᴰ ]

module _
  {C : Category Cob CHom-ℓ}
  (Pᴰ : StructureOver C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Pᴰ = StructureOver Pᴰ

  open Categoryᴰ
  StructureOver→Catᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ
  StructureOver→Catᴰ .Hom[_][_,_] = Pᴰ.Hom[_][_,_]
  StructureOver→Catᴰ .idᴰ = Pᴰ.idᴰ
  StructureOver→Catᴰ ._⋆ᴰ_ = Pᴰ._⋆ᴰ_
  StructureOver→Catᴰ .⋆IdLᴰ _ =
    Σ≡Prop (λ _ → Pᴰ.isPropHomᴰ) (C.⋆IdL _)
  StructureOver→Catᴰ .⋆IdRᴰ _ =
    Σ≡Prop (λ _ → Pᴰ.isPropHomᴰ) (C.⋆IdR _)
  StructureOver→Catᴰ .⋆Assocᴰ _ _ _ =
    Σ≡Prop (λ _ → Pᴰ.isPropHomᴰ) (C.⋆Assoc _ _ _)
  StructureOver→Catᴰ .isSetHomᴰ = isProp→isSet Pᴰ.isPropHomᴰ

  hasPropHomsStructureOver : hasPropHoms StructureOver→Catᴰ
  hasPropHomsStructureOver _ _ _ = Pᴰ.isPropHomᴰ
