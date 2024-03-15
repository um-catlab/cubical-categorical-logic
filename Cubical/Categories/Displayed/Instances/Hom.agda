{-
  The Hom profunctor viewed as a 2-sided discrete fibration.

  This is just an instance of Constructions.Graph but it's common
  enough to be given its own module.

  https://ncatlab.org/nlab/show/two-sided+fibration#twosided_discrete_fibrations
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Hom where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Profunctor.Relator as Relator hiding (Hom)
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Base.DisplayOverProjections
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Constructions.Graph

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS ℓR : Level

module _ (C : Category ℓC ℓC') where
  Hom : Categoryᴰ (C ×C C) ℓC' ℓC'
  Hom = Graph {C = C}{D = C} (Relator.Hom C)

  hasPropHomsHom = hasPropHomsGraph (Relator.Hom C)

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C
  open Functorᴰ
  ID : Functorᴰ (Δ C) (Unitᴰ C) (Hom C)
  ID = mkFunctorᴰPropHoms (hasPropHomsHom C)
    (λ x → C.id)
    (λ f → C.⋆IdR _ ∙ sym (C.⋆IdL _))
