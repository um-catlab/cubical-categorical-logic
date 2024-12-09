{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Transport

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.Reindex.Base hiding (π)
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open CartesianLift

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where

  private
    module C = Category C
    module D = Category D
    F*Dᴰ = reindex Dᴰ F
    module R = HomᴰReasoning Dᴰ
    module F*Dᴰ = Categoryᴰ F*Dᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  hasPropHomsReindex : hasPropHoms Dᴰ → hasPropHoms (reindex Dᴰ F)
  hasPropHomsReindex = λ z {c} {c'} f → z (F-hom F f)

  module _
    {c : C .ob}{c' : C .ob}
    {dᴰ' : Dᴰ.ob[ F ⟅ c' ⟆ ]}{f : C [ c , c' ]}
    where
    reflectsCartesianLifts
      : CartesianLift Dᴰ dᴰ' (F ⟪ f ⟫)
      → CartesianLift F*Dᴰ dᴰ' f
    reflectsCartesianLifts F⟪f⟫-lift .f*yᴰ = F⟪f⟫-lift .f*yᴰ
    reflectsCartesianLifts F⟪f⟫-lift .π = F⟪f⟫-lift .π
    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .fst gfᴰ =
      F⟪f⟫-lift .isCartesian .fst (R.reind (F .F-seq _ _) gfᴰ)
    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .snd .fst gfᴰ =
      R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ (R.≡in $ F⟪f⟫-lift .isCartesian .snd .fst _)
      ∙ (sym $ R.reind-filler _ _)

    reflectsCartesianLifts F⟪f⟫-lift .isCartesian .snd .snd gᴰ =
      R.rectify $ R.≡out $
      ((R.≡in $ congP (λ _ → F⟪f⟫-lift .isCartesian .fst)
        -- TODO: add reindReind⁻ to Reasoning
        $ transportTransport⁻ (λ i → Dᴰ.Hom[ F .F-seq _ _ i ][ _ , _ ])
          (gᴰ Dᴰ.⋆ᴰ F⟪f⟫-lift .π))
      ∙ (R.≡in $ F⟪f⟫-lift .isCartesian .snd .snd gᴰ))

  isFibrationReindex : isFibration Dᴰ → isFibration (reindex Dᴰ F)
  isFibrationReindex isFibDᴰ _ _ = reflectsCartesianLifts (isFibDᴰ _ _)
