module Cubical.Categories.LocallySmall.Instances.Functor.SmallFibered.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation

open Category
open Categoryᴰ
open Liftω

module _
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  (C : SmallCategory ℓC ℓC')
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C =  SmallCategory C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  open SmallFibNatTrans

  SMALL-FIBERED-FUNCTOR : SmallFibersCategoryᴰ D _ (SmallFiberedFunctor C Dᴰ) _
  SMALL-FIBERED-FUNCTOR .Hom[_][_,_] f xᴰ yᴰ =
    SmallFibNatTrans C Dᴰ f (xᴰ .lowerω) (yᴰ .lowerω)
  SMALL-FIBERED-FUNCTOR .idᴰ = idSFTrans _
  SMALL-FIBERED-FUNCTOR ._⋆ᴰ_ α β = seqSFTrans α β
  SMALL-FIBERED-FUNCTOR .⋆IdLᴰ {f = f} α =
    makeSFNatTransPath (D.⋆IdL _) (λ x → Dᴰ.⋆IdLᴰ (α .N-ob x))
  SMALL-FIBERED-FUNCTOR .⋆IdRᴰ α =
    makeSFNatTransPath (D.⋆IdR _) (λ x → Dᴰ.⋆IdRᴰ (α .N-ob x))
  SMALL-FIBERED-FUNCTOR .⋆Assocᴰ α β γ =
    makeSFNatTransPath
      (D.⋆Assoc _ _ _)
      (λ x → Dᴰ.⋆Assocᴰ (α .N-ob x) (β .N-ob x) (γ .N-ob x))
  SMALL-FIBERED-FUNCTOR .isSetHomᴰ = isSetSFNatTrans _ _ _
