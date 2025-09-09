module Cubical.Categories.Displayed.Presheaf.Constructions.Unit.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Functorᴰ

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  where
  reindUnitEq : PresheafᴰEq (reind α (UnitPshᴰ {Cᴰ = Cᴰ})) UnitPshᴰ
  reindUnitEq = Eq.refl , Eq.refl

  reindUnit : reind α (UnitPshᴰ {Cᴰ = Cᴰ}) ≡ UnitPshᴰ
  reindUnit =
    Functorᴰ≡ (λ _ → funExt λ _ → Σ≡Prop (λ _ → isPropIsSet) refl)
    λ fᴰ → refl

  reindUnitIsoⱽ : PshIsoⱽ (reind α (UnitPshᴰ {Cᴰ = Cᴰ})) UnitPshᴰ
  reindUnitIsoⱽ = eqToPshIsoⱽ reindUnitEq

module _ {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {Q : Presheaf D ℓQ}
  where
  -- for some reason this can't be inlined. Is this an Agda bug?
  reindFuncUnitEq : PresheafᴰEq (reindFunc F (UnitPshᴰ {Cᴰ = Dᴰ}{P = Q})) UnitPshᴰ
  reindFuncUnitEq = (Eq.refl , Eq.refl)

  reindFuncUnitIsoⱽ : PshIsoⱽ (reindFunc F (UnitPshᴰ {Cᴰ = Dᴰ}{P = Q})) UnitPshᴰ
  reindFuncUnitIsoⱽ = eqToPshIsoⱽ reindFuncUnitEq

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  where
  UnitPshᴰ≅UnitPshᴰ : PshIsoᴰ {Cᴰ = Cᴰ} α (UnitPshᴰ {P = P}) (UnitPshᴰ {P = Q})
  UnitPshᴰ≅UnitPshᴰ =
    invPshIsoⱽ reindUnitIsoⱽ
    ⋆PshIsoⱽᴰ reindPshIsoPshIsoᴰ α (UnitPshᴰ {P = Q})

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓP}
  {α : P ≡ Q}
  where
  UnitPshᴰ≡UnitPshᴰ :
    PathP
      (λ i → Presheafᴰ (α i) Cᴰ ℓ-zero)
      (UnitPshᴰ {P = P})
      (UnitPshᴰ {P = Q})
  UnitPshᴰ≡UnitPshᴰ = sym reindUnit ◁ reindPathToPshIsoPathP α UnitPshᴰ

open Section
open PshHomᴰ
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (F : GlobalSection Cᴰ) where
  UnitPsh→UnitPshᴰ : PshSection F (UnitPshᴰ {P = UnitPsh {C = C}})
  UnitPsh→UnitPshᴰ .N-obᴰ _ = tt
  UnitPsh→UnitPshᴰ .N-homᴰ = refl
