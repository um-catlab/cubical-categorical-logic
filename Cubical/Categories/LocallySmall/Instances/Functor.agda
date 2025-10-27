module Cubical.Categories.LocallySmall.Instances.Functor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Prod using (_×ω_; _,_)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base as LocallySmall
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Displayed

open Category
open Categoryᴰ

module _
  {D : Category Dob DHom-ℓ}
  {Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ}
  ((Cob , C) : SmallCategory ℓC ℓC')
  (Dᴰ : SmallFibersCategoryᴰ D Dobᴰ-ℓ Dobᴰ DHom-ℓᴰ)
  where
  private
    module C =  CategoryNotation C
    module D =  CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
  open SmallFibNatTrans
  FIBER-FUNCTOR : Categoryᴰ D (λ d → Functor C Dᴰ.v[ d ]) _
  FIBER-FUNCTOR .Hom[_][_,_] = SmallFibNatTrans Dᴰ
  FIBER-FUNCTOR .idᴰ = idSFTrans _
  FIBER-FUNCTOR ._⋆ᴰ_ α β = seqSFTrans α β
  FIBER-FUNCTOR .⋆IdLᴰ {f = f} α =
    makeSFNatTransPath (D.⋆IdL _) (λ x → Dᴰ.⋆IdLᴰ (α .N-ob x))
  FIBER-FUNCTOR .⋆IdRᴰ α =
    makeSFNatTransPath (D.⋆IdR _) (λ x → Dᴰ.⋆IdRᴰ (α .N-ob x))
  FIBER-FUNCTOR .⋆Assocᴰ α β γ =
    makeSFNatTransPath
      (D.⋆Assoc _ _ _)
      (λ x → Dᴰ.⋆Assocᴰ (α .N-ob x) (β .N-ob x) (γ .N-ob x))
  FIBER-FUNCTOR .isSetHomᴰ = isSetSFNatTrans _ _ _
