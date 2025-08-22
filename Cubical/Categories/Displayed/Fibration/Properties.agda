{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Fibration.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Profunctor.General

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.FunctorComprehension
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functorᴰ
open NatTransᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  private
    module Cᴰ = Fibers Cᴰ
    module C = Category C
  module _ {x y : C .ob}{yᴰ : Cᴰ.ob[ y ]}{f : C [ x , y ]} where
    module _ (cL : CartesianLift Cᴰ yᴰ f) where
      private
        module cL = CartesianLift cL
      open UniversalElementⱽ
      CartesianLift→CartesianLift' : CartesianLift' Cᴰ yᴰ f
      CartesianLift→CartesianLift' .vertexⱽ = cL.f*yᴰ
      CartesianLift→CartesianLift' .elementⱽ = Cᴰ.idᴰ Cᴰ.⋆ᴰ cL.π
      CartesianLift→CartesianLift' .universalⱽ .fst = cL.isCartesian .fst
      CartesianLift→CartesianLift' .universalⱽ {z} {zᴰ} {g} .snd .fst gfᴰ =
        Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ⟩
          ∙ cL.βCL
      CartesianLift→CartesianLift' .universalⱽ {z} {zᴰ} {g} .snd .snd gᴰ =
        Cᴰ.rectify $ Cᴰ.≡out $ cL.introCL≡ $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ⟩

  isFibration→isFibration' : isFibration Cᴰ → isFibration' Cᴰ
  isFibration→isFibration' cLs cᴰ' f = CartesianLift→CartesianLift' (cLs cᴰ' f)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  CartesianLiftF : isFibration Cᴰ → Functorⱽ (C /C Cᴰ) Cᴰ
  CartesianLiftF cLs = CartesianLift'F _ (isFibration→isFibration' cLs)

