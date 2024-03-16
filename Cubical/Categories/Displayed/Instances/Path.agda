{-
  Paths between objects as a category displayed over C × C.

  If C is univalent, this is equivalent to the IsoComma category.

  Universal property: a displayed functor into this is a proof that
  two functors are equal.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Path where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator as Relator hiding (Hom)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Preorder hiding (Section; reindex)
open import Cubical.Categories.Displayed.Properties

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _  (C : Category ℓC ℓC') where
  module C = Category C
  private
      PathC' : Preorderᴰ (C ×C C) _ _
      PathC' .Preorderᴰ.ob[_] (c , d) = c ≡ d
      PathC' .Preorderᴰ.Hom[_][_,_] (f , g) c≡c' d≡d' =
        PathP (λ i → C.Hom[ c≡c' i , d≡d' i ]) f g
      PathC' .Preorderᴰ.idᴰ = λ i → C.id
      PathC' .Preorderᴰ._⋆ᴰ_ f≡f' g≡g' = λ i → f≡f' i ⋆⟨ C ⟩ g≡g' i
      PathC' .Preorderᴰ.isPropHomᴰ = isOfHLevelPathP' 1 C.isSetHom _ _

  PathC : Categoryᴰ (C ×C C) ℓC ℓC'
  PathC = Preorderᴰ→Catᴰ PathC'

  hasPropHomsPathC : hasPropHoms PathC
  hasPropHomsPathC = hasPropHomsPreorderᴰ PathC'

  -- The universal functor into PathC
  Refl : Functorᴰ (Δ C) (Unitᴰ C) PathC
  Refl = mkFunctorᴰPropHoms hasPropHomsPathC (λ {c} tt → refl) λ {f} tt → refl

  -- Universal data from PathC
module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F1 F2 : Functor D C}
         where
  -- todo: one of these should be defined using the other
  FunctorPathC→Path : ∀ (Fᴰ : Functorᴰ (F1 ,F F2) (Unitᴰ D) (PathC C)) → F1 ≡ F2
  FunctorPathC→Path Fᴰ =
    Functor≡ (λ c → Fᴰ.F-obᴰ {c} tt ) λ f → Fᴰ.F-homᴰ {f = f} tt
    where module Fᴰ = Functorᴰ Fᴰ

  SectionPathC→Path : ∀ (Fᴰ : Section (reindex (PathC C) (F1 ,F F2))) → F1 ≡ F2
  SectionPathC→Path Fᴰ = Functor≡ Fᴰ.F-ob Fᴰ.F-hom
    where module Fᴰ = Section Fᴰ
