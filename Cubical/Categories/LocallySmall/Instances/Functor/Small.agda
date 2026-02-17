module Cubical.Categories.LocallySmall.Instances.Functor.Small where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Small
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open Category

module _ (C : SmallCategory ℓC ℓC')(D : GloballySmallCategory Dob ℓD') where
  private
    module C = SmallCategory C
    module D = CategoryNotation D
  FUNCTOR : GloballySmallCategory (Functor C.cat D) (ℓ-max (ℓ-max ℓC ℓC') ℓD')
  FUNCTOR .Hom[_,_] F G = NatTrans F G
  FUNCTOR .Category.id = idTrans _
  FUNCTOR .Category._⋆_ = seqTrans
  FUNCTOR .Category.⋆IdL α = makeNatTransPath $ funExt λ _ → D.⋆IdL _
  FUNCTOR .Category.⋆IdR α = makeNatTransPath $ funExt λ _ → D.⋆IdR _
  FUNCTOR .Category.⋆Assoc α β γ = makeNatTransPath $ funExt λ _ →
    D.⋆Assoc _ _ _
  FUNCTOR .Category.isSetHom = isSetIso (NatTransIsoΣ _ _)
    (isSetΣ
      (isSetΠ (λ _ → D.isSetHom))
      λ _ → isProp→isSet (isPropImplicitΠ2 (λ _ _ → isPropΠ (λ f → D.isSetHom _ _))))
