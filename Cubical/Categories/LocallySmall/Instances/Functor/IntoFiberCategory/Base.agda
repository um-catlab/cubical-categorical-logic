{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory.Base where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
-- import Cubical.Categories.LocallySmall.Functor.Base as LocallySmallF
-- open import Cubical.Categories.LocallySmall.Functor.IntoFiberCategory
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
-- open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Constructions.ChangeOfObjects
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ

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
  open NatTransDefs C Dᴰ
  open NatTrans

  FUNCTOR : Categoryᴰ D Functor _
  FUNCTOR .Hom[_][_,_] = NatTrans
  FUNCTOR .idᴰ = idTrans _
  FUNCTOR ._⋆ᴰ_ α β = seqTrans α β
  FUNCTOR .⋆IdLᴰ {f = f} α =
    makeNatTransPath (D.⋆IdL _) (λ x → Dᴰ.⋆IdLᴰ (α .N-ob x))
  FUNCTOR .⋆IdRᴰ α =
    makeNatTransPath (D.⋆IdR _) (λ x → Dᴰ.⋆IdRᴰ (α .N-ob x))
  FUNCTOR .⋆Assocᴰ α β γ =
    makeNatTransPath
      (D.⋆Assoc _ _ _)
      (λ x → Dᴰ.⋆Assocᴰ (α .N-ob x) (β .N-ob x) (γ .N-ob x))
  FUNCTOR .isSetHomᴰ = isSetNatTrans _ _ _

  module _ (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x}) where
    FUNCTOR-EQ : Categoryᴰ D (FunctorEq D-⋆) _
    FUNCTOR-EQ =
      ChangeOfDisplayedObjectsᴰ.ChangeOfObjectsᴰ FUNCTOR
        (FunctorEq→Functor D-⋆ _)

    open LocallySmallFᴰ.Functorᴰ
    FUNCTOR→FUNCTOR-EQ :
      LocallySmallFᴰ.Functorⱽ FUNCTOR FUNCTOR-EQ
    FUNCTOR→FUNCTOR-EQ .F-obᴰ =
      Functor→FunctorEq D-⋆ _
    FUNCTOR→FUNCTOR-EQ .F-homᴰ α =
      natTrans
        (NatTransDefs.NatTrans.N-ob α)
        (NatTransDefs.NatTrans.N-hom α)
    FUNCTOR→FUNCTOR-EQ .F-idᴰ =
      makeNatTransPath refl λ _ → refl
    FUNCTOR→FUNCTOR-EQ .F-seqᴰ _ _ =
      makeNatTransPath refl λ _ → refl

    FUNCTOR-EQ→FUNCTOR :
      LocallySmallFᴰ.Functorⱽ FUNCTOR-EQ FUNCTOR
    FUNCTOR-EQ→FUNCTOR =
      ChangeOfDisplayedObjectsᴰ.πᴰ
        FUNCTOR (FunctorEq→Functor D-⋆ _)
