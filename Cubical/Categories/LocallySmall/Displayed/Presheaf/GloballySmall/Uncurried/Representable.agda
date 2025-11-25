module Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.Uncurried.Representable where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category.Base as SmallCat
import Cubical.Categories.Presheaf.Base as SmallPsh
import Cubical.Categories.Functor.Base as SmallFunctor

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.IntoFiberCategory.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Graph.Presheaf.GloballySmall.Base
open import Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.Uncurried.Base

open Σω
open Liftω
open Functor

module _ where
  open SmallCategoryVariables
  open SmallCategory
  module _
    {c : C .ob}
    (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
    where
    private
      module C = SmallCategory C
      module Cᴰ = SmallCategoryᴰ Cᴰ

    -- TODO
    -- implement the general conversion between curried and uncurried
    -- presheaves
    _[-][-,_] : Cᴰ.obᴰ c → Presheafⱽ c Cᴰ ℓCᴰ'
    _[-][-,_] cᴰ .F-ob (liftω (x , xᴰ , f)) = liftω (Cᴰ.Hom[ f ][ liftω xᴰ , liftω cᴰ ] , Cᴰ.isSetHomᴰ)
    _[-][-,_] cᴰ .F-hom (f , fᴰ , the-≡) gᴰ =
      Cᴰ.reind the-≡ (fᴰ Cᴰ.⋆ᴰ gᴰ)
    _[-][-,_] cᴰ .F-id = funExt λ gᴰ →
      Cᴰ.rectify $ Cᴰ.≡out $ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⋆IdLᴰ _
    _[-][-,_] cᴰ .F-seq (f , fᴰ , the-≡) (g , gᴰ , the-≡') = funExt λ gᴰ →
      Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ Cᴰ.⋆Assocᴰ _ _ _
        ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
        ∙ Cᴰ.reind-filler _ _
