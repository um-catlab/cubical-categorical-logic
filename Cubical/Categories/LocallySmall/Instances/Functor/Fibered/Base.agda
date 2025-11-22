{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Instances.Functor.Fibered.Base where

open import Cubical.Foundations.Prelude

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Constructions.ChangeOfObjects
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

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
  open FibNatTransDefs C Dᴰ
  open FibNatTrans

  FIBERED-FUNCTOR : Categoryᴰ D FiberedFunctor _
  FIBERED-FUNCTOR .Hom[_][_,_] = FibNatTrans
  FIBERED-FUNCTOR .idᴰ = idFibTrans _
  FIBERED-FUNCTOR ._⋆ᴰ_ α β = seqFibTrans α β
  FIBERED-FUNCTOR .⋆IdLᴰ {f = f} α =
    makeFibNatTransPath (D.⋆IdL _) (λ x → Dᴰ.⋆IdLᴰ (α .N-ob x))
  FIBERED-FUNCTOR .⋆IdRᴰ α =
    makeFibNatTransPath (D.⋆IdR _) (λ x → Dᴰ.⋆IdRᴰ (α .N-ob x))
  FIBERED-FUNCTOR .⋆Assocᴰ α β γ =
    makeFibNatTransPath
      (D.⋆Assoc _ _ _)
      (λ x → Dᴰ.⋆Assocᴰ (α .N-ob x) (β .N-ob x) (γ .N-ob x))
  FIBERED-FUNCTOR .isSetHomᴰ = isSetFibNatTrans _ _ _

  module _ (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x}) where
    FIBERED-FUNCTOR-EQ : Categoryᴰ D (FiberedFunctorEq D-⋆) _
    FIBERED-FUNCTOR-EQ =
      ChangeOfDisplayedObjectsᴰ.ChangeOfObjectsᴰ FIBERED-FUNCTOR
        (FiberedFunctorEq→FiberedFunctor D-⋆ _)

    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ :
      Functorⱽ FIBERED-FUNCTOR FIBERED-FUNCTOR-EQ
    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ .Functorᴰ.F-obᴰ =
      FiberedFunctor→FiberedFunctorEq D-⋆ _
    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ .Functorᴰ.F-homᴰ α =
      natTrans
        (FibNatTransDefs.FibNatTrans.N-ob α)
        (FibNatTransDefs.FibNatTrans.N-hom α)
    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ .Functorᴰ.F-idᴰ =
      makeFibNatTransPath refl λ _ → refl
    FIBERED-FUNCTOR→FIBERED-FUNCTOR-EQ .Functorᴰ.F-seqᴰ _ _ =
      makeFibNatTransPath refl λ _ → refl

    FIBERED-FUNCTOR-EQ→FIBERED-FUNCTOR :
      Functorⱽ FIBERED-FUNCTOR-EQ FIBERED-FUNCTOR
    FIBERED-FUNCTOR-EQ→FIBERED-FUNCTOR =
      ChangeOfDisplayedObjectsᴰ.πᴰ
        FIBERED-FUNCTOR (FiberedFunctorEq→FiberedFunctor D-⋆ _)
