{-

  reindexing The Iso category over a monoidal category along strong
  monoidal functors gives a displayed monoidal category. This can
  probably be generalized, but it would require isofibrations and so
  this direct argument is a little simpler e.g., because everything
  hasPropHoms.

  TODO: shouldn't this be about IsoComma? should IsoComma just be
  defined as reindex of Iso?

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Arrow.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
import      Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.Monoidal
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Monoidal
import Cubical.Categories.Displayed.Instances.Arrow.Base as Arrow
open import Cubical.Categories.Displayed.Instances.Arrow.Properties

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open MonoidalCategoryᴰ
open TensorStrᴰ
open MonoidalStrᴰ
open NatTrans
open NatIso
open Functor

module _ (M : MonoidalCategory ℓC ℓC') where
  private
    module M = MonoidalCategory M
  Iso : MonoidalCategoryᴰ (M ×M M) ℓC' ℓC'
  Iso .Cᴰ = Arrow.Iso M.C
  Iso .monstrᴰ = TensorPropᴰ→TensorStrᴰ (M ×M M) (Iso .Cᴰ)
    hasPropHomsCᴰ
    MP
    where
      hasPropHomsCᴰ = (Arrow.hasPropHomsIso M.C)
      open MonoidalPropᴰ
      MP : MonoidalPropᴰ (M ×M M) (Arrow.Iso M.C)
      MP .tenstrᴰ .unitᴰ = idCatIso
      MP .tenstrᴰ .─⊗ᴰ─ = mkPropHomsFunctor hasPropHomsCᴰ
        (λ { (x≅x' , y≅y') → F-Iso {F = M.─⊗─} (BP.CatIso× M.C M.C x≅x' y≅y') })
        λ { ((f-sq , _) , (g-sq , _)) →
          sym (M.─⊗─ .F-seq _ _ )
          ∙ cong₂ M._⊗ₕ_ f-sq g-sq
          ∙ M.─⊗─ .F-seq _ _
          , _
          }
      MP .MonoidalPropᴰ.αᴰ⟨_,_,_⟩ x≅x' y≅y' z≅z' =
        sym (M.α .trans .N-hom _) , _
      MP .MonoidalPropᴰ.α⁻¹ᴰ⟨_,_,_⟩ _ _ _ =
        sym (symNatIso M.α .trans .N-hom _) , _
      MP .MonoidalPropᴰ.ηᴰ⟨_⟩ x≅x' =
        sym (M.η .trans .N-hom _)
        , _
      MP .MonoidalPropᴰ.η⁻¹ᴰ⟨_⟩ x≅x' =
        sym (symNatIso M.η .trans .N-hom _)
        , _
      MP .MonoidalPropᴰ.ρᴰ⟨_⟩ _ = sym (M.ρ .trans .N-hom _) , _
      MP .MonoidalPropᴰ.ρ⁻¹ᴰ⟨_⟩ _ = sym (symNatIso M.ρ .trans .N-hom _) , _

module _ {M : MonoidalCategory ℓC ℓC'} {N : MonoidalCategory ℓD ℓD'}
         (G H : StrongMonoidalFunctor M N)
  where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module G = StrongMonoidalFunctor G
    module H = StrongMonoidalFunctor H

  IsoComma : MonoidalCategoryᴰ M ℓD' ℓD'
  IsoComma =
    reindex (Iso N) (G ,F H)
      (Arrow.hasPropHomsIso N.C) (isIsoFibrationIso N.C)
