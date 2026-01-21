{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.Morphism.Lift where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits
open import Cubical.Categories.Yoneda
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Bifunctor

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
