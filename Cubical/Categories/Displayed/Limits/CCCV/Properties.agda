{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CCCV.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation hiding (_⇒_)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open PshIso

module _ (CC : CartesianCategory ℓC ℓC') where
  open CartesianCategory CC
  module _ (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
    private
      module Cᴰ = Fibers Cᴰ
    open CartesianClosedCategoryⱽ hiding (Cᴰ)
    mkCCCⱽ : CartesianClosedCategoryⱽ CC _ _
    mkCCCⱽ .CCⱽ .CartesianCategoryⱽ.Cᴰ = Cᴰ
    mkCCCⱽ .CCⱽ .CartesianCategoryⱽ.termⱽ x .fst = {!!}
    mkCCCⱽ .CCⱽ .CartesianCategoryⱽ.termⱽ x .snd = Isos→PshIso {!!} λ x₁ y f p →
      {!!}
    mkCCCⱽ .CCⱽ .CartesianCategoryⱽ.bpⱽ xᴰ yᴰ = {!!}
    mkCCCⱽ .CCⱽ .CartesianCategoryⱽ.cartesianLifts = {!!}
    mkCCCⱽ .lrⱽ = {!!}
    mkCCCⱽ .expⱽ xᴰ yᴰ .fst = {!!}
    mkCCCⱽ .expⱽ xᴰ yᴰ .snd = Isos→PshIso _ (λ x y f p →
      sym $ Cᴰ.rectify $ Cᴰ.≡out $
        sym (Cᴰ.reind-filler _ _) ∙ {!!})
    mkCCCⱽ .forallⱽ Aᴰ .fst = {!!}
    mkCCCⱽ .forallⱽ Aᴰ .snd = Isos→PshIso {!!}
      λ x y f p →
        sym (Cᴰ.rectify $ Cᴰ.≡out $ sym (Cᴰ.reind-filler _ _)
          ∙ {!!})
