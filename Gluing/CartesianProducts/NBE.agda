{-

  Normalization by evaluation proof for free cartesian category using
  the gluing construction.

-}

{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianProducts.NBE where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Presheaf.CCC

open import Cubical.Categories.Constructions.Free.Category.Quiver as FC
  hiding (rec)
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base as FCC
  hiding (rec)
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver as PQ
  hiding (_×_)
import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Fibration.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Base
open import Cubical.Categories.Displayed.Instances.Presheaf.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct


open import Cubical.Data.FinSet
open import Cubical.Data.FinSet.Constructors

private
  variable ℓQ ℓQ' ℓC ℓC' : Level

open Category
open Functor
open Categoryᴰ
open Section
open NatTrans
open Cubical.Categories.Constructions.Elements.Contravariant
open CartesianOver


FinOrd : ∀ ℓ → Type (ℓ-suc ℓ)
FinOrd ℓ = TypeWithStr ℓ isFinOrd

module _ (Q : ×Quiver ℓQ ℓQ') where
  F×1 = FreeCartesianCategory Q

  -- TODO #1: define the category of renamings.
  Ren₀ : Type _
  Ren₀ = Σ[ X ∈ FinOrd ℓ-zero ]
    (⟨ X ⟩ → F×1 .fst .ob)

  _∈v_ : F×1 .fst .ob → Ren₀ → Type _
  A ∈v Γ = Σ[ x ∈ ⟨ Γ .fst ⟩ ]
    A ≡ Γ .snd x -- bad! pick a different, inductive representation of renamings

  Ren₁ : Ren₀ → Ren₀ → Type _
  Ren₁ Γ Δ = ∀ (x : ⟨ Δ .fst ⟩) → Δ .snd x ∈v Γ

  Ren : Category _ _
  Ren = {!!}

  RenToTm : Functor Ren (F×1 .fst)
  RenToTm = {!!}

  data NF1 : ∀ x y (f : F×1 .fst [ x , y ]) → Type {!!} where
    _,ₑ_ : ∀ {x y₁ y₂}{f₁ f₂}
      → NF1 x y₁ f₁ → NF1 x y₂ f₂
      → NF1 x (y₁ PQ.× y₂) (FCC.⟨ f₁ , f₂ ⟩)

  -- make a presheaf out of NF1, this gets you a logical relation, but
  -- that only gets you normal forms for base types. Need
  -- reify/reflect yoga for full NBE
