module Cubical.Categories.Displayed.Presheaf.Constructions.Lift.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Lift.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

open Bifunctorᴰ
open Functorᴰ

open isIsoOver

open PshHom
open PshIso

open PshHomᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  LiftHomⱽ : ∀ {ℓ'} → PshHomⱽ Pᴰ (LiftPshᴰ Pᴰ ℓ')
  LiftHomⱽ .N-obᴰ = λ z → lift z
  LiftHomⱽ .N-homᴰ = refl

  LiftIsoⱽ : ∀ {ℓ'} → PshIsoⱽ Pᴰ (LiftPshᴰ Pᴰ ℓ')
  LiftIsoⱽ .fst = LiftHomⱽ
  LiftIsoⱽ .snd .inv = λ a z → z .lower
  LiftIsoⱽ .snd .rightInv b q = refl
  LiftIsoⱽ .snd .leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf C ℓP} {Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  {α : P ≡ Q}
  where
  Lift-Path :
    ∀ (αᴰ : PathP (λ i → Presheafᴰ (α i) Cᴰ ℓPᴰ) Pᴰ Qᴰ)
    → PathP (λ i → Presheafᴰ (α i) Cᴰ (ℓ-max ℓPᴰ ℓ'))
        (LiftPshᴰ Pᴰ ℓ')
        (LiftPshᴰ Qᴰ ℓ')
  Lift-Path αᴰ i = LiftPshᴰ (αᴰ i) _
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Q : Presheaf C ℓQ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  -- TODO: naming...
  Lift-F-Homᴰ : ∀ {α : PshHom P Q} (αᴰ : PshHomᴰ α Pᴰ Qᴰ) → PshHomᴰ α (LiftPshᴰ Pᴰ ℓ) (LiftPshᴰ Qᴰ ℓ')
  Lift-F-Homᴰ αᴰ .N-obᴰ pᴰ = lift (αᴰ .N-obᴰ (pᴰ .lower))
  Lift-F-Homᴰ αᴰ .N-homᴰ {fᴰ = fᴰ}{pᴰ = pᴰ} i =
    lift (αᴰ .N-homᴰ {fᴰ = fᴰ}{pᴰ = pᴰ .lower} i)

  Lift-F-Isoᴰ : ∀ {α : PshIso P Q} (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) → PshIsoᴰ α (LiftPshᴰ Pᴰ ℓ) (LiftPshᴰ Qᴰ ℓ')
  Lift-F-Isoᴰ αᴰ .fst = Lift-F-Homᴰ (αᴰ .fst)
  Lift-F-Isoᴰ αᴰ .snd .inv _ qᴰ = lift (αᴰ .snd .inv _ (qᴰ .lower))
  Lift-F-Isoᴰ αᴰ .snd .rightInv p pᴰ i =
    lift (αᴰ .snd .rightInv p (pᴰ .lower) i)
  Lift-F-Isoᴰ αᴰ .snd .leftInv q qᴰ i =
    lift (αᴰ .snd .leftInv q (qᴰ .lower) i)

module _{C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  reindLiftEq : PresheafᴰEq (reind α (LiftPshᴰ Qᴰ ℓ')) (LiftPshᴰ (reind α Qᴰ) ℓ')
  reindLiftEq = Eq.refl , Eq.refl

  reindLift : reind α (LiftPshᴰ Qᴰ ℓ') ≡ LiftPshᴰ (reind α Qᴰ) ℓ'
  reindLift = Functorᴰ≡ (λ xᴰ → refl) (λ _ → refl)

  reindLiftIsoⱽ : PshIsoⱽ (reind α (LiftPshᴰ Qᴰ ℓ')) (LiftPshᴰ (reind α Qᴰ) ℓ')
  reindLiftIsoⱽ = eqToPshIsoⱽ reindLiftEq
