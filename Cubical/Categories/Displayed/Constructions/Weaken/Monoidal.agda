{-

  If M and N are monoidal categories, then weaken M.C N.C can be given
  the structure of a displayed monoidal category.

-}
module Cubical.Categories.Displayed.Constructions.Weaken.Monoidal where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ (M : MonoidalCategory ℓC ℓC') (N : MonoidalCategory ℓD ℓD') where
  open Category
  open MonoidalCategoryᴰ
  open Functorᴰ
  open Functor
  open NatTransᴰ
  open NatIsoᴰ
  open isIsoᴰ
  open NatTrans
  open NatIso
  open isIso
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
  -- God bless the new Auto! solves everything starting from unitᴰ!
  weaken : MonoidalCategoryᴰ M ℓD ℓD'
  weaken .Cᴰ = Wk.weaken M.C N.C
  weaken .monstrᴰ .MonoidalStrᴰ.tenstrᴰ .TensorStrᴰ.─⊗ᴰ─ .F-obᴰ = N.─⊗─ .F-ob
  weaken .monstrᴰ .MonoidalStrᴰ.tenstrᴰ .TensorStrᴰ.─⊗ᴰ─ .F-homᴰ = N.─⊗─ .F-hom
  weaken .monstrᴰ .MonoidalStrᴰ.tenstrᴰ .TensorStrᴰ.─⊗ᴰ─ .F-idᴰ = N.─⊗─ .F-id
  weaken .monstrᴰ .MonoidalStrᴰ.tenstrᴰ .TensorStrᴰ.─⊗ᴰ─ .F-seqᴰ = N.─⊗─ .F-seq
  weaken .monstrᴰ .MonoidalStrᴰ.tenstrᴰ .TensorStrᴰ.unitᴰ = N.unit
  weaken .monstrᴰ .MonoidalStrᴰ.αᴰ .transᴰ .N-obᴰ = N.α .trans .N-ob
  weaken .monstrᴰ .MonoidalStrᴰ.αᴰ .transᴰ .N-homᴰ = N.α .trans .N-hom
  weaken .monstrᴰ .MonoidalStrᴰ.αᴰ .nIsoᴰ xᴰ .invᴰ = N.α .nIso xᴰ .inv
  weaken .monstrᴰ .MonoidalStrᴰ.αᴰ .nIsoᴰ xᴰ .secᴰ = N.α .nIso xᴰ .sec
  weaken .monstrᴰ .MonoidalStrᴰ.αᴰ .nIsoᴰ xᴰ .retᴰ = N.α .nIso xᴰ .ret
  weaken .monstrᴰ .MonoidalStrᴰ.ηᴰ .transᴰ .N-obᴰ = N-ob (N.η .trans)
  weaken .monstrᴰ .MonoidalStrᴰ.ηᴰ .transᴰ .N-homᴰ = N-hom (N.η .trans)
  weaken .monstrᴰ .MonoidalStrᴰ.ηᴰ .nIsoᴰ xᴰ .invᴰ = N.η .nIso xᴰ .inv
  weaken .monstrᴰ .MonoidalStrᴰ.ηᴰ .nIsoᴰ xᴰ .secᴰ = N.η .nIso xᴰ .sec
  weaken .monstrᴰ .MonoidalStrᴰ.ηᴰ .nIsoᴰ xᴰ .retᴰ = N.η .nIso xᴰ .ret
  weaken .monstrᴰ .MonoidalStrᴰ.ρᴰ .transᴰ .N-obᴰ = N-ob (N.ρ .trans)
  weaken .monstrᴰ .MonoidalStrᴰ.ρᴰ .transᴰ .N-homᴰ = N-hom (N.ρ .trans)
  weaken .monstrᴰ .MonoidalStrᴰ.ρᴰ .nIsoᴰ xᴰ .invᴰ = N.ρ .nIso xᴰ .inv
  weaken .monstrᴰ .MonoidalStrᴰ.ρᴰ .nIsoᴰ xᴰ .secᴰ = N.ρ .nIso xᴰ .sec
  weaken .monstrᴰ .MonoidalStrᴰ.ρᴰ .nIsoᴰ xᴰ .retᴰ = N.ρ .nIso xᴰ .ret
  weaken .monstrᴰ .MonoidalStrᴰ.pentagonᴰ = N.pentagon
  weaken .monstrᴰ .MonoidalStrᴰ.triangleᴰ = N.triangle
