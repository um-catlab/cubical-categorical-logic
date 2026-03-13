{-# OPTIONS --lossy-unification #-}
module Gluing.CartesianClosedCategory.Normalization.Renamings where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Empty
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Instances.Free.CartesianCategory.ProductQuiver
  using (×Quiver; module ×Quiver)
import Cubical.Categories.Instances.Free.CartesianCategory.Forded as FCC
open import Cubical.Categories.Instances.Free.CartesianClosedCategory.Forded as FCCC
open import
  Cubical.Categories.Instances.Free.CartesianClosedCategory.Quiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc; PSHIdL; PSHπ₁NatEq; PSH×aF-seq)
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.Cartesian
open import Cubical.Categories.Displayed.Instances.Presheaf.Eq.CartesianClosed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
  using (EqCCCⱽ→CCCⱽ)
open import Cubical.Categories.Presheaf.Nerve using (Nerve; Nerve-pres-bp)
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHomStrict
open PshHom

module _ (Q : ×⇒Quiver ℓQ ℓQ') where
  private
    module Q = ×⇒Quiver Q
    ℓ = ℓ-max ℓQ ℓQ'

  -- ×Quiver for renamings: CCC objects as base, no generators
  REN-×Quiver : ×Quiver ℓQ ℓQ'
  REN-×Quiver .×Quiver.ob = Q.obExpr
  REN-×Quiver .×Quiver.Q .QuiverOver.mor = ⊥*
  REN-×Quiver .×Quiver.Q .QuiverOver.dom ()
  REN-×Quiver .×Quiver.Q .QuiverOver.cod ()

  -- Free cartesian category of renamings
  REN : CartesianCategory _ _
  REN = FCC.FreeCartesianCategory REN-×Quiver

  |REN| : Category _ _
  |REN| = CartesianCategory.C REN

  -- Renaming morphism type
  Ren : |REN| .ob → |REN| .ob → Type _
  Ren Γ Δ = |REN| [ Γ , Δ ]

  -- Free CCC
  FREE-CCC : CartesianClosedCategory _ _
  FREE-CCC = FreeCartesianClosedCategory Q

  private module FREE-CCC' = CartesianClosedCategory FREE-CCC

  |FREE-CCC| : Category _ _
  |FREE-CCC| = FREE-CCC'.C

  -- Embedding ι : REN → FREE-CCC
  ι : Functor |REN| |FREE-CCC|
  ι = FCC.rec REN-×Quiver (CartesianClosedCategory.CC FREE-CCC)
    (FCC.mkElimInterpᴰ (λ A → A) (λ ()))

  ι-ob : |REN| .ob → |FREE-CCC| .ob
  ι-ob = ι .F-ob

  -- Nerve functor
  nerve : Functor |FREE-CCC| (PRESHEAF |REN| ℓ)
  nerve = Nerve ι

  nerve-pres-bp : preservesProvidedBinProducts nerve
    (CartesianClosedCategory.CC FREE-CCC .CartesianCategory.bp)
  nerve-pres-bp = Nerve-pres-bp ι
    (CartesianClosedCategory.CC FREE-CCC .CartesianCategory.bp)

  -- Displayed category infrastructure
  RENᴰ : Categoryᴰ |REN| ℓ-zero ℓ-zero
  RENᴰ = Unitᴰ.Unitᴰ |REN|

  PSHᴰ : Categoryᴰ (PRESHEAF |REN| ℓ) _ _
  PSHᴰ = PRESHEAFᴰ RENᴰ ℓ ℓ

  module PSHᴰ' = Categoryᴰ PSHᴰ

  private
    PSH-CC : CartesianCategory _ _
    PSH-CC = Cartesian-PRESHEAF |REN| ℓ

  PSHᴰCᴰ : Categoryᴰ (PRESHEAF |REN| ℓ) _ _
  PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ
    (EqCCⱽ→CCⱽ PSHAssoc PSHᴰ isCartesianⱽPSHᴰ)

  PSHᴰCartesianClosedⱽ : CartesianClosedCategoryⱽ PSH-CC _ _
  PSHᴰCartesianClosedⱽ = EqCCCⱽ→CCCⱽ PSH-CC PSHAssoc PSHIdL PSHπ₁NatEq PSH×aF-seq PSHᴰ isCartesianClosedⱽPSHᴰ
