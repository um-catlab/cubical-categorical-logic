{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct as BP hiding (π₁ ; π₂)
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Presheaf.StrictHom

open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ
open PshHomStrict
open PshHom
open PshIso

private
  variable
    ℓ ℓ' ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}where
  ℓPSHᴰ = ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')
  PSHᴰExponentials : Exponentialsⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHIdL (BPⱽ+Fibration→AllLRⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHᴰBPⱽ PSHᴰFibration)
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .fst = Pᴰ ⇒PshLarge Qᴰ
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.isos R3@(R , Rᴰ , α) =
    PshHom Rᴰ (α *Strict (Pᴰ ⇒PshLarge Qᴰ))
      Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (Pᴰ ⇒PshLarge Qᴰ) ⟩
    PshHom (α PushStrict Rᴰ) (Pᴰ ⇒PshLarge Qᴰ)
      Iso⟨ ⇒PshLarge-UMP Pᴰ Qᴰ ⟩
    PshHom (((α PushStrict Rᴰ)) ×Psh Pᴰ) Qᴰ
      Iso⟨ precomp⋆PshHom-Iso (FrobeniusReciprocity (PshHomStrict→Eq α) Rᴰ Pᴰ) ⟩
    PshHom (α PushStrict (Rᴰ ×Psh (α *Strict Pᴰ))) Qᴰ
      Iso⟨ invIso (Push⊣* (PshHomStrict→Eq α) (Rᴰ ×Psh (α *Strict Pᴰ)) Qᴰ) ⟩
    PshHom (Rᴰ ×Psh (α *Strict Pᴰ)) (α *Strict Qᴰ)
      ∎Iso
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.nat = {!!}

  PSHᴰ∀ : UniversalQuantifiers (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL PSHAssoc PSHᴰFibration PSHBP PSHπ₁NatEq PSH×aF-seq
  PSHᴰ∀ = {!!}

  isCartesianClosedⱽPSHᴰ : isCartesianClosedⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL  PSHBP PSHπ₁NatEq PSH×aF-seq
  isCartesianClosedⱽPSHᴰ .fst = isCartesianⱽPSHᴰ
  isCartesianClosedⱽPSHᴰ .snd .fst = PSHᴰExponentials
  isCartesianClosedⱽPSHᴰ .snd .snd = {!!}
  -- isCartesianⱽPSHᴰ .fst = PSHᴰTerminalsⱽ
  -- isCartesianⱽPSHᴰ .snd .fst = PSHᴰBPⱽ
  -- isCartesianⱽPSHᴰ .snd .snd = PSHᴰFibration
