{-
  Natural isomorphisms displayed over natural isomorphisms.
-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.NaturalIsomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Functorᴰ
open NatIso
open isIso
open NatTransᴰ
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  record NatIsoᴰ {F : Functor C D}{G : Functor C D}
    (α : NatIso F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ)
    : Type (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ (ℓ-max ℓCᴰ' ℓDᴰ')))) where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    field
      transᴰ : NatTransᴰ (α .trans) Fᴰ Gᴰ
      nIsoᴰ : ∀ {x} (xᴰ : Cᴰ.ob[ x ]) → isIsoᴰ Dᴰ (α .nIso x) (transᴰ .N-obᴰ xᴰ)

  module _ {F : Functor C D}{G : Functor C D}
    (α : NatIso F G)
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) (Gᴰ : Functorᴰ G Cᴰ Dᴰ) where
    open NatTrans
    open NatIsoᴰ
    private
      module Dᴰ = Categoryᴰ Dᴰ
    mkNatIsoPropHom : hasPropHoms Dᴰ
      → (∀ {x} xᴰ → Dᴰ.Hom[ α .trans ⟦ x ⟧ ][ Fᴰ .F-obᴰ xᴰ , Gᴰ .F-obᴰ xᴰ ])
      → (∀ {x} xᴰ → Dᴰ.Hom[ α .nIso x .inv ][ Gᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ xᴰ ])
      → NatIsoᴰ α Fᴰ Gᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .transᴰ .N-obᴰ = αᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .transᴰ .N-homᴰ {f = f} fᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.invᴰ = α⁻ᴰ xᴰ
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.secᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _
    mkNatIsoPropHom isPropHomDᴰ αᴰ α⁻ᴰ .nIsoᴰ xᴰ .isIsoᴰ.retᴰ =
      propHomsFiller Dᴰ isPropHomDᴰ _ _ _
