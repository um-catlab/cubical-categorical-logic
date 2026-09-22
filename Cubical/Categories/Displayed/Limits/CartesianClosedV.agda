{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.CartesianClosedV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.More
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open PshIso

record CartesianClosedCategoryⱽ (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  constructor cartesiancategoryⱽ
  open CartesianCategory CC
  field
    CCⱽ : CartesianCategoryⱽ C ℓCᴰ ℓCᴰ'
  open CartesianCategoryⱽ CCⱽ public
  field
    lrⱽ : AllLRⱽ Cᴰ
    expⱽ : Exponentialsⱽ Cᴰ lrⱽ
    forallⱽ : UniversalQuantifiers Cᴰ bp cartesianLifts

record CartesianClosedCategoryᴰ (CCC : CartesianClosedCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) : Type ((ℓ-max (ℓ-max (ℓ-max (ℓ-suc ℓC) (ℓ-suc ℓC')) (ℓ-suc ℓCᴰ)) (ℓ-suc ℓCᴰ'))) where
  open CartesianClosedCategory CCC
  field
    CCᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'

  open CartesianCategoryᴰ CCᴰ public
  field
    expᴰ : AllExponentiableᴰ Cᴰ bp bpᴰ exps

  open ExponentialsᴰNotation {C = C}{Cᴰ = Cᴰ} bp bpᴰ exps expᴰ public

module _ (CCC : CartesianClosedCategory ℓC ℓC') (CCCⱽ : CartesianClosedCategoryⱽ (CartesianClosedCategory.CC CCC) ℓCᴰ ℓCᴰ') where
  open CartesianClosedCategoryⱽ CCCⱽ
  open CartesianClosedCategoryᴰ hiding (Cᴰ)
  open CartesianClosedCategory CCC
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ : CartesianClosedCategoryᴰ CCC ℓCᴰ ℓCᴰ'
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ .CCᴰ = CartesianCategoryⱽ→CartesianCategoryᴰ (CartesianClosedCategory.CC CCC) CCⱽ
  CartesianClosedCategoryⱽ→CartesianClosedCategoryᴰ .expᴰ {A} Aᴰ {B} Bᴰ =
    ∀+Expⱽ+lifts⇒Expᴰ
      (cartesianLifts Aᴰ ((A ⇒ B) × A) π₂)
      (lrⱽ _)
      (cartesianLifts Bᴰ ((A ⇒ B) × A) app)
      (expⱽ _ _)
      (λ _ _ → cartesianLifts _ _ _)
      (forallⱽ .∀Ob _)
