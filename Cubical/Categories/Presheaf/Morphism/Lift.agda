{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Morphism.Lift where

open import Cubical.Foundations.Prelude



open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr ℓs : Level

open Category
open Contravariant
open UniversalElement
open PshHom
open PshIso

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp) ℓq where
  LiftPshIso : PshIso P (LiftPsh P ℓq)
  LiftPshIso .trans .N-ob = λ c z → lift z
  LiftPshIso .trans .N-hom = λ _ _ _ _ → refl
  LiftPshIso .nIso c .fst = λ z → z .lower
  LiftPshIso .nIso c .snd .fst _ = refl
  LiftPshIso .nIso c .snd .snd _ = refl

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp) {ℓq} {ℓr} where
  PshHomPsh-LiftPshIso :
    PshIso
      (PshHomPsh {ℓp = ℓr} P)
      (PshHomPsh {ℓp = ℓr} (LiftPsh P ℓq))
  PshHomPsh-LiftPshIso =
    Isos→PshIso (λ Q → postcomp⋆PshHom-Iso (LiftPshIso P ℓq))
      (λ _ _ _ _ → ⋆PshHomAssoc _ _ _)
