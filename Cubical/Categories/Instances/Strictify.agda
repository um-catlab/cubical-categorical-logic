module Cubical.Categories.Instances.Strictify where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels

import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.FullImage
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.StrictHom

private
  variable ℓ ℓC ℓC' ℓD ℓD' : Level

open Category
open Functor

module _ (C : Category ℓC ℓC') where
  private
    module C = Category C

  YonedaStrictify : Category ℓC (ℓ-max ℓC ℓC')
  YonedaStrictify = FullImage (YOStrict {C = C})

  toYonedaStrictify : Functor C YonedaStrictify
  toYonedaStrictify = ToFullImage YOStrict

  fromYonedaStrictify : Functor YonedaStrictify C
  fromYonedaStrictify = inv isFullyFaithfulYOStrict

  private
    Hom≃ : ∀ {x y} → C [ x , y ] ≃ PshHomStrict (C [-, x ]) (C [-, y ])
    Hom≃ {x}{y} = YOStrict .F-hom , isFullyFaithfulYOStrict x y

  fromYonedaStrictify∘toYonedaStrictify≡Id : fromYonedaStrictify ∘F toYonedaStrictify ≡ Id
  fromYonedaStrictify∘toYonedaStrictify≡Id = Functor≡ (λ _ → refl) (λ f → retEq Hom≃ f)

  toYonedaStrictify∘fromYonedaStrictify≡Id : toYonedaStrictify ∘F fromYonedaStrictify ≡ Id
  toYonedaStrictify∘fromYonedaStrictify≡Id = Functor≡ (λ _ → refl) (λ f → secEq Hom≃ f)
