{-# OPTIONS --lossy-unification #-}
module Gluing.Forded.CartesianClosedCategory.Conservativity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Functions.FunExtEquiv
open import Cubical.Data.Quiver.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Constructions.Free.Category.Forded as FC
open import Cubical.Categories.Constructions.Free.CartesianCategory.Forded as FCC
open import Cubical.Categories.Constructions.Free.CartesianClosedCategory.Forded as FCCC
open import
  Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
  hiding (_×_)
open import
  Cubical.Categories.Constructions.Free.CartesianClosedCategory.Quiver
  hiding (_×_)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Limits.CartesianV' as V'
import Cubical.Categories.Displayed.Instances.Terminal.Base as Unitᴰ
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
  hiding (PRESHEAFᴰ)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base as PshBase
  using (PRESHEAFᴰ; PSHAssoc)
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.StrictHom

private
  variable ℓQ ℓQ' : Level

open Category
open Functor
open Categoryᴰ
open Section
open PshHomStrict
open PshHom

module _ (Q : Quiver ℓQ ℓQ') where
  private
    module Q = QuiverOver (Q .snd)
    ×Q = Quiver→×Quiver Q
    module ×Q = ×Quiver ×Q
    ×⇒Q = Quiver→×⇒Quiver Q
    module ×⇒Q = ×⇒Quiver ×⇒Q


  FREE-1,× : CartesianCategory _ _
  FREE-1,× = FreeCartesianCategory ×Q

  FREE-1,×,⇒ : CartesianClosedCategory _ _
  FREE-1,×,⇒ = FreeCartesianClosedCategory ×⇒Q

  private
    module FREE-1,× = CartesianCategory FREE-1,×
    module FREE-1,×,⇒ = CartesianClosedCategory FREE-1,×,⇒

    ℓ = ℓ-max ℓQ ℓQ'

    PSH = PRESHEAF FREE-1,×.C ℓ

  -- ı : FC.Interp Q FREE-1,×.C
  -- ı : FC.Interp Q FREE-1,×.C
  -- ı .HetQG._$g_ = ↑_
  -- ı .HetQG._<$g>_ = FCC.↑ₑ (Quiver→×Quiver Q)

  ⊆ : Functor FREE-1,×.C FREE-1,×,⇒.C
  ⊆ = FCC.rec ×Q FREE-1,×,⇒.CC (mkElimInterpᴰ (λ o → CCCExpr.↑ o) (FCCC.↑ₑ ×⇒Q))

  extension : Functor FREE-1,×,⇒.C PSH
  extension = FCCC.rec ×⇒Q (CCC-PRESHEAF FREE-1,×.C ℓQ)
    (mkElimInterpᴰ
       (λ o → YOStrict ⟅ ProdExpr.↑ o ⟆)
       (λ f → YOStrict ⟪ FCC.↑ₑ ×Q f ⟫))

  commutes : YOStrict ≡ extension ∘F ⊆
  commutes = {!!}

  comp-Faithful : isFaithful (extension ∘F ⊆)
  comp-Faithful = subst isFaithful commutes isFaithfulYOStrict

  -- TODO move this
  module _ {ℓA ℓA' ℓB ℓB' ℓC ℓC'}
    {A : Category ℓA ℓA'}{B : Category ℓB ℓB'}{C : Category ℓC ℓC'}
    (F : Functor A B)(G : Functor B C) where
    isFaithful-GF→isFaithful-F : isFaithful (G ∘F F) → isFaithful F
    isFaithful-GF→isFaithful-F faith x y f g p =
      faith x y f g (congS (λ Ff → G ⟪ Ff ⟫) p)

  ⊆-Faithful : isFaithful ⊆
  ⊆-Faithful = isFaithful-GF→isFaithful-F ⊆ extension comp-Faithful

  nerve : Functor FREE-1,×,⇒.C (PRESHEAF FREE-1,×.C _)
  nerve = reindPshFStrict ⊆ ∘F YOStrict

  private
    FREE-1,×ᴰ : Categoryᴰ FREE-1,×.C ℓ-zero ℓ-zero
    FREE-1,×ᴰ = Unitᴰ.Unitᴰ FREE-1,×.C

    PSHᴰ = PRESHEAFᴰ FREE-1,×ᴰ ℓ ℓ

    module PSHᴰ = Categoryᴰ PSHᴰ

    PSHᴰCartesianⱽEq : isCartesianⱽ PSHAssoc PSHᴰ
    PSHᴰCartesianⱽEq = isCartesianⱽPSHᴰ

    PSHᴰCartesianⱽ : V'.CartesianCategoryⱽ PSH _ _
    PSHᴰCartesianⱽ = EqCCⱽ→CCⱽ PSHAssoc PSHᴰ PSHᴰCartesianⱽEq

    PSHᴰCᴰ : Categoryᴰ PSH _ _
    PSHᴰCᴰ = V'.CartesianCategoryⱽ.Cᴰ PSHᴰCartesianⱽ

  S : Section nerve PSHᴰCᴰ
  S = FCCC.elimLocal ×⇒Q {!!} {!!} {!!}
