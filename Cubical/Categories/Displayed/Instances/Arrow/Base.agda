{-
  Arrow category and sub-category of Isos as categories displayed over C × C.

  Universal property: a section of the Arrow bundle is a natural
  transformation between functors, section of the Iso bundle is a
  natural isomorphism

-}
module Cubical.Categories.Displayed.Instances.Arrow.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Morphism
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Graph
open import Cubical.Categories.Displayed.Instances.PropertyOver
open import Cubical.Categories.Displayed.Instances.TotalCategory
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Weaken.Base
open import Cubical.Categories.Displayed.Instances.Weaken.Properties
open import Cubical.Categories.Instances.TotalCategory hiding (Fst; Snd)
open import Cubical.Categories.Bifunctor hiding (Fst; Snd)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor

module _ (C : Category ℓC ℓC') where
  Arrow : Categoryᴰ (C ×C C) ℓC' ℓC'
  Arrow = Graph (HomBif C)

  Arrow∫wk : Categoryᴰ (∫C (weaken C C)) ℓC' ℓC'
  Arrow∫wk = EqReindex.reindex Arrow ∫wk→× Eq.refl λ _ _ → Eq.refl

  hasPropHomsArrow : hasPropHoms Arrow
  hasPropHomsArrow = hasPropHomsGraph (HomBif C)

  IsMono : Categoryᴰ (∫C Arrow) (ℓ-max ℓC ℓC') ℓ-zero
  IsMono = PropertyOver _ (λ x → isMonic C (x .snd))

  Mono : Categoryᴰ  (C ×C C) _ _
  Mono = ∫Cᴰ Arrow IsMono

  IsIso : Categoryᴰ (∫C Arrow) ℓC' ℓ-zero
  IsIso = PropertyOver _ (λ x → isIso C (x .snd))

  hasContrHomsIsIso : hasContrHoms IsIso
  hasContrHomsIsIso = hasContrHomsPropertyOver (∫C Arrow) _

  Iso : Categoryᴰ (C ×C C) ℓC' ℓC'
  Iso = ∫Cᴰ Arrow IsIso

  Iso∫wk : Categoryᴰ (∫C (weaken C C)) ℓC' ℓC'
  Iso∫wk = EqReindex.reindex Iso ∫wk→× Eq.refl λ _ _ → Eq.refl

  hasPropHomsIso : hasPropHoms Iso
  hasPropHomsIso =
    hasPropHoms∫Cᴰ {Cᴰ = Arrow} IsIso hasPropHomsArrow
      (hasContrHoms→hasPropHoms IsIso hasContrHomsIsIso)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F1 F2 : Functor D C}
         where
  ArrowReflection : ∀ (Fᴰ : Section (F1 ,F F2) (Arrow C)) → F1 ⇒ F2
  ArrowReflection Fᴰ = natTrans Fᴰ.F-obᴰ Fᴰ.F-homᴰ
    where module Fᴰ = Section Fᴰ

  arrIntroS : F1 ⇒ F2 → Section (F1 ,F F2) (Arrow C)
  arrIntroS α = mkPropHomsSection (hasPropHomsArrow C)
    (NatTrans.N-ob α)
    (NatTrans.N-hom α)

  IsoReflection : ∀ (Fᴰ : Section (F1 ,F F2) (Iso C)) → F1 ≅ᶜ F2
  IsoReflection Fᴰ = record
    { trans = natTrans
       (λ x → Fᴰ.F-obᴰ x .fst )
        λ f → Fᴰ.F-homᴰ f .fst
    ; nIso = λ x → Fᴰ.F-obᴰ x .snd
    }
    where module Fᴰ = Section Fᴰ

  isoIntroS : F1 ≅ᶜ F2 → Section (F1 ,F F2) (Iso C)
  isoIntroS α = mkPropHomsSection (hasPropHomsIso C)
    (λ x → NatTrans.N-ob (α .NatIso.trans) x , α .NatIso.nIso x)
    (λ {x} {y} f → NatTrans.N-hom (α .NatIso.trans) f , tt)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {F : Functor D (C ×C C)}
         where
  IsoReflection' : ∀ (Fᴰ : Section F (Iso C))
    → (Fst C C ∘F F) ≅ᶜ (Snd C C ∘F F)
  IsoReflection' Fᴰ =
    IsoReflection (reindS' (Eq.refl , Eq.refl) Fᴰ)
