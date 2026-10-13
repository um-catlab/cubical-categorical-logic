module Cubical.Categories.Presheaf.StrictHom.Bifunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Functions.FunExtEquiv

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

open import Cubical.Data.Sigma

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR : Level

open Category
open Functor
open NatTrans
open PshHomStrict

module _ {C : Category ℓC ℓC'} where
  PshHomBifStrict : ∀ (ℓP ℓQ : Level) →
    Bifunctor ((PRESHEAF C ℓP) ^op) (PRESHEAF C ℓQ) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓQ))
  PshHomBifStrict ℓP ℓQ = mkBifunctorSep BifSep
    where
    BifSep : BifunctorSep ((PRESHEAF C ℓP) ^op) (PRESHEAF C ℓQ) (SET (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓP) ℓQ))
    BifSep .BifunctorSep.Bif-ob P Q = PshHomStrict P Q , isSetPshHomStrict P Q
    BifSep .BifunctorSep.Bif-homL α Q β = α ⋆PshHomStrict β
    BifSep .BifunctorSep.Bif-homR P β α = α ⋆PshHomStrict β
    BifSep .BifunctorSep.SepBif-RL-commute α β = funExt λ γ → makePshHomStrictPath refl
    BifSep .BifunctorSep.Bif-L-id = funExt λ _ → makePshHomStrictPath refl
    BifSep .BifunctorSep.Bif-L-seq α α' = funExt λ _ → makePshHomStrictPath refl
    BifSep .BifunctorSep.Bif-R-id = funExt λ _ → makePshHomStrictPath refl
    BifSep .BifunctorSep.Bif-R-seq β β' = funExt λ _ → makePshHomStrictPath refl
