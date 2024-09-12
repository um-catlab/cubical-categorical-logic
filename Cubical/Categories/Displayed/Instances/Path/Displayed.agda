{-
  Paths between objects as a category displayed over C × C.

  If C is univalent, this is equivalent to the IsoComma category.

  (Right) Universal property: a section of the Path bundle is a path
  between section

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Path.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.TotalCategory as TotalCategory
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More as BPᴰ
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.StructureOver

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _  {C : Category ℓC ℓC'}
          (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
          where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    open StructureOver
    PathCᴰ' : StructureOver (∫C {C = C} (Cᴰ ×ᴰ Cᴰ)) _ _
    PathCᴰ' .ob[_] (c , cᴰ , cᴰ') = cᴰ ≡ cᴰ'
    PathCᴰ' .Hom[_][_,_] (f , fᴰ , fᴰ') p q =
      PathP (λ i → Cᴰ.Hom[ f ][ p i , q i ]) fᴰ fᴰ'
    PathCᴰ' .idᴰ i = Cᴰ.idᴰ
    PathCᴰ' ._⋆ᴰ_ fᴰ≡fᴰ' gᴰ≡gᴰ' i = fᴰ≡fᴰ' i Cᴰ.⋆ᴰ gᴰ≡gᴰ' i
    PathCᴰ' .isPropHomᴰ = isOfHLevelPathP' 1 Cᴰ.isSetHomᴰ _ _
  open Categoryᴰ
  PathCᴰ : Categoryᴰ (∫C {C = C} (Cᴰ ×ᴰ Cᴰ)) _ _
  PathCᴰ = StructureOver→Catᴰ PathCᴰ'

  hashPropHomsPathCᴰ : hasPropHoms PathCᴰ
  hashPropHomsPathCᴰ = hasPropHomsStructureOver PathCᴰ'

  open Section
  Refl : Section (∫F {C = C} (Δᴰ Cᴰ)) PathCᴰ
  Refl .F-obᴰ (c , cᴰ) = refl
  Refl .F-homᴰ (f , fᴰ) = refl
  Refl .F-idᴰ = refl
  Refl .F-seqᴰ _ _ = refl

  module _ {D : Category ℓD ℓD'}
           {F : Functor D C}
           (M N : Section F Cᴰ)
           where
   -- TODO: do we need any of the alternate formulations?
   PathReflection :
     Section (TotalCategory.intro F (introS F M N)) PathCᴰ
     → M ≡ N
   PathReflection M≡N i .F-obᴰ d = M≡N .F-obᴰ d i
   PathReflection M≡N i .F-homᴰ f = M≡N .F-homᴰ f i
   PathReflection M≡N i .F-idᴰ j = M≡N .F-idᴰ j i
   PathReflection M≡N i .F-seqᴰ f g j = M≡N .F-seqᴰ f g j i
