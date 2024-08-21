{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
-- open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Constructions.TotalCategory
  as TotalCat
  hiding (intro)
open import Cubical.Categories.Constructions.TotalCategory.More
  as TotalCat
open import Cubical.Categories.Displayed.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Constructions.TotalCategory.More
open import Cubical.Categories.Displayed.Fibration.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ
module _ {C : Category ℓC ℓC'}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (Dᴰ : Categoryᴰ (∫C Cᴰ) ℓDᴰ ℓDᴰ')
  where
  private
    module R = HomᴰReasoning Dᴰ
  open CartesianOver
  isFibᴰ∫Cᴰ : AllCartesianOvers Cᴰ → AllCartesianOvers Dᴰ → AllCartesianOvers (∫Cᴰ Cᴰ Dᴰ)
  isFibᴰ∫Cᴰ isFibCᴰ isFibDᴰ (cᴰ' , dᴰ') f .f*cᴰ' =
    isFibCᴰ cᴰ' f .f*cᴰ'
    , isFibDᴰ dᴰ' (f , (isFibCᴰ cᴰ' f .π)) .f*cᴰ'
  isFibᴰ∫Cᴰ isFibCᴰ isFibDᴰ (cᴰ' , dᴰ') f .π =
    isFibCᴰ cᴰ' f .π
    , isFibDᴰ dᴰ' (f , (isFibCᴰ cᴰ' f .π)) .π
  isFibᴰ∫Cᴰ isFibCᴰ isFibDᴰ cᴰ' f .isCartesian cᴰ'' g (gfᴰ , gfᴰᴰ) = uniqueExists
    ((corec (isFibCᴰ _ _) _ _ gfᴰ)
    , corec (isFibDᴰ _ _) _ _
      (R.reind (ΣPathP (refl , (sym (corec-β (isFibCᴰ _ _) _ _ gfᴰ)))) gfᴰᴰ))
    (ΣPathP ((corec-β (isFibCᴰ _ _) _ _ gfᴰ) ,
      R.≡[]-rectify (R.≡[]∙ _ _ (corec-β (isFibDᴰ _ _) _ _ _) (R.reind-filler-sym _ _))))
    (λ _ → (∫Cᴰ Cᴰ Dᴰ) .isSetHomᴰ _ _)
    λ (gᴰ , gᴰᴰ) p → ΣPathP
      ( (cong (corec (isFibCᴰ _ _) _ _) (sym (cong fst p))
        ∙ sym (corec-η (isFibCᴰ _ _) _ _ gᴰ))
      , (R.≡[]-rectify (R.≡[]∙ _ _
          (congP (λ _ → corec (isFibDᴰ _ _) _ _) {!!})
          {!!}))
      )
