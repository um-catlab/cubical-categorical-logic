{-
  Yoneda strictification of a displayed category.
-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Strictify where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Instances.Strictify
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.FullImage
  hiding (invᴰ)
import      Cubical.Categories.Displayed.Instances.FullImage as FIᴰ
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.StrictHom

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Categoryᴰ
open Functorᴰ
open NatTransᴰ
open NatIsoᴰ
open isIsoᴰ
open PshHomStrict
open PshHomStrictᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰf = Fibers Cᴰ
    module Cᴰ = Categoryᴰ Cᴰ

  YonedaStrictifyᴰ
    : Categoryᴰ (YonedaStrictify C)
        ℓCᴰ
        (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  YonedaStrictifyᴰ = FullImageᴰ (YOStrict {C = C}) (YOStrictᴰ Cᴰ)

  toYonedaStrictifyᴰ : Functorᴰ (toYonedaStrictify C) Cᴰ YonedaStrictifyᴰ
  toYonedaStrictifyᴰ = ToFullImageᴰ (YOStrict {C = C}) (YOStrictᴰ Cᴰ)

  fromYonedaStrictifyᴰ : Functorᴰ (fromYonedaStrictify C) YonedaStrictifyᴰ Cᴰ
  fromYonedaStrictifyᴰ =
    FIᴰ.invᴰ (YOStrict {C = C}) isFullyFaithfulYOStrict
      (isFullyFaithfulYOStrictᴰ Cᴰ)

  fromYonedaStrictifyᴰ∘toYonedaStrictifyᴰ≡Idᴰ
    : PathP (λ i → Functorᴰ (fromYonedaStrictify∘toYonedaStrictify≡Id C i) Cᴰ Cᴰ)
        (fromYonedaStrictifyᴰ ∘Fᴰ toYonedaStrictifyᴰ) 𝟙ᴰ⟨ Cᴰ ⟩
  fromYonedaStrictifyᴰ∘toYonedaStrictifyᴰ≡Idᴰ =
    invᴰ∘ToFullImageᴰ≡Idᴰ (YOStrict {C = C}) isFullyFaithfulYOStrict
      (isFullyFaithfulYOStrictᴰ Cᴰ)

  toYonedaStrictifyᴰ∘fromYonedaStrictifyᴰ≡Idᴰ
    : PathP (λ i → Functorᴰ (toYonedaStrictify∘fromYonedaStrictify≡Id C i)
              YonedaStrictifyᴰ YonedaStrictifyᴰ)
        (toYonedaStrictifyᴰ ∘Fᴰ fromYonedaStrictifyᴰ) 𝟙ᴰ⟨ YonedaStrictifyᴰ ⟩
  toYonedaStrictifyᴰ∘fromYonedaStrictifyᴰ≡Idᴰ =
    ToFullImageᴰ∘invᴰ≡Idᴰ (YOStrict {C = C}) isFullyFaithfulYOStrict
      (isFullyFaithfulYOStrictᴰ Cᴰ)

  YonedaStrictifyᴰ'
    : Categoryᴰ (YonedaStrictify C)
        ℓCᴰ
        (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
  YonedaStrictifyᴰ' .ob[_] = Cᴰ.ob[_]
  YonedaStrictifyᴰ' .Hom[_][_,_] α xᴰ yᴰ =
    PshHomStrictᴰ α (Cᴰ [-][-, xᴰ ]) (Cᴰ [-][-, yᴰ ])
  YonedaStrictifyᴰ' .idᴰ = idPshHomStrictᴰ
  YonedaStrictifyᴰ' ._⋆ᴰ_ = _⋆PshHomStrictᴰ_
  YonedaStrictifyᴰ' .⋆IdLᴰ _ = refl
  YonedaStrictifyᴰ' .⋆IdRᴰ _ = refl
  YonedaStrictifyᴰ' .⋆Assocᴰ _ _ _ = refl
  YonedaStrictifyᴰ' .isSetHomᴰ = isSetPshHomStrictᴰ _ _ _

  -- FullImageᴰ gives the right definition for YonedaStrictifyᴰ
  YonedaStrictifyᴰ≡ : YonedaStrictifyᴰ ≡ YonedaStrictifyᴰ'
  YonedaStrictifyᴰ≡ i .ob[_] = Cᴰ.ob[_]
  YonedaStrictifyᴰ≡ i .Hom[_][_,_] α xᴰ yᴰ =
    PshHomStrictᴰ α (Cᴰ [-][-, xᴰ ]) (Cᴰ [-][-, yᴰ ])
  YonedaStrictifyᴰ≡ i .idᴰ = idPshHomStrictᴰ
  YonedaStrictifyᴰ≡ i ._⋆ᴰ_ = _⋆PshHomStrictᴰ_
  YonedaStrictifyᴰ≡ i .⋆IdLᴰ _ = refl
  YonedaStrictifyᴰ≡ i .⋆IdRᴰ _ = refl
  YonedaStrictifyᴰ≡ i .⋆Assocᴰ _ _ _ = refl
  YonedaStrictifyᴰ≡ i .isSetHomᴰ = isSetPshHomStrictᴰ _ _ _
