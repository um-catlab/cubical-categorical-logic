module Cubical.Categories.Displayed.Instances.Family.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Instances.Family.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
private
  variable
    ℓ ℓ' ℓC ℓC' ℓD ℓD' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open NatTransᴰ
open PshIso
open isIso
open UniversalElement

-- Lifting of functors
--
-- F : C → D
--
-- Fam(F) : Functorⱽ Fam(C) Fam(D)
module _ {ℓ} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module C = Category C
    module FamC = Fibers (Fam {ℓ = ℓ} C)
    module FamD = Fibers (Fam {ℓ = ℓ} D)
  FamF : Functor C D → Functorⱽ (Fam {ℓ = ℓ} C) (Fam D)
  FamF F .F-obᴰ c x = F .F-ob (c x)
  FamF F .F-homᴰ f x = F .F-hom (f x)
  FamF F .F-idᴰ = funExt (λ _ → F .F-id)
  FamF F .F-seqᴰ fᴰ gᴰ = funExt (λ _ → F .F-seq _ _)

  module _ {F G : Functor C D} (α : NatTrans F G) where
    FamNT : NatTransⱽ (FamF F) (FamF G)
    FamNT .N-obᴰ = λ xᴰ x₁ → N-ob α (xᴰ x₁)
    FamNT .N-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ = FamD.rectifyOut {a = x}{b = y}{aᴰ = λ x₁ → F .F-ob (xᴰ x₁)}{bᴰ = λ z → G .F-ob (yᴰ z)}
      (ΣPathP (refl , (funExt (λ x → α .N-hom (fᴰ x)))))

module _ {ℓ} {C : Category ℓC ℓC'} where
  private
    module C = Category C
    module FamC = Fibers (Fam {ℓ = ℓ} C)
  FamFId : NatTransᴰ (idTrans Id) (FamF {ℓ = ℓ} (Id {C = C})) Idᴰ
  FamFId .N-obᴰ = λ xᴰ x₁ → C .id
  FamFId .N-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ = FamC.rectifyOut {a = x}{b = y}{aᴰ = xᴰ}{bᴰ = yᴰ}
    (ΣPathP (refl , (funExt (λ _ → idTrans (Id {C = C}) .N-hom _))))

-- TODO: HACK ALERT!!!
module _ {ℓ} {C : Category ℓC ℓC'} {F : Functor C C} (α : NatTrans Id F) where
  private
    module C = Category C
    module FamC = Fibers (Fam {ℓ = ℓ} C)
  Fam-PtNT : NatTransⱽ Idᴰ (FamF {ℓ = ℓ} F)
  Fam-PtNT .N-obᴰ = λ xᴰ x₁ → N-ob α (xᴰ x₁)
  Fam-PtNT .N-homᴰ {x} {y} {f} {xᴰ} {yᴰ} fᴰ = FamC.rectifyOut {a = x}{b = y}{aᴰ = xᴰ}{bᴰ = λ z → F .F-ob (yᴰ z)}
    (ΣPathP (refl , funExt (λ _ → α .N-hom _)))
