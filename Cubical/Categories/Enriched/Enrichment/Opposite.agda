{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Enriched.Enrichment.Opposite where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.NaturalTransformation using (NatIso)
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Dual
open import Cubical.Categories.Monoidal.Properties using (ρ⁻¹⟨unit⟩≡η⁻¹⟨unit⟩)
open import Cubical.Categories.Reasoning.Core
open import Cubical.Categories.Enriched.Enrichment.Base

private
  variable
    ℓV ℓV' ℓC ℓC' : Level

module _ {V : MonoidalCategory ℓV ℓV'} {C : Category ℓC ℓC'} (ℰ : Enrichment C V) where
  private
    module V = MonoidalCategory V
    module ℰ = Enrichment ℰ
  open Reasoning V.C

  _^opᴱ : Enrichment (C ^op) (V ^co)
  _^opᴱ .Enrichment.VE[_,_] X Y = ℰ.VE[ Y , X ]
  _^opᴱ .Enrichment.id = ℰ.id
  _^opᴱ .Enrichment.seq X Y Z = ℰ.seq Z Y X
  _^opᴱ .Enrichment.⇄-agree = ℰ.⇄-agree
  _^opᴱ .Enrichment.⋆IdL X Y = ℰ.⋆IdR Y X
  _^opᴱ .Enrichment.⋆IdR X Y = ℰ.⋆IdL Y X
  _^opᴱ .Enrichment.⋆Assoc X Y Z W =
      cong (V.α⁻¹⟨ _ , _ , _ ⟩ V.⋆_) (sym (ℰ.⋆Assoc W Z Y X))
    ∙ pullˡ (V.α .NatIso.nIso _ .isIso.sec)
    ∙ V.⋆IdL _
  _^opᴱ .Enrichment.⌜id⌝ = ℰ.⌜id⌝
  _^opᴱ .Enrichment.⌜⋆⌝ f g = ℰ.⌜⋆⌝ g f ∙ cong (V._⋆ ((ℰ.⌜ g ⌝ V.⊗ₕ ℰ.⌜ f ⌝) V.⋆ ℰ.seq _ _ _)) (sym (ρ⁻¹⟨unit⟩≡η⁻¹⟨unit⟩ V))
