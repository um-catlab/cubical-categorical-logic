{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.CartesianClosed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

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
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
import Cubical.Categories.Displayed.Limits.CartesianV' as Path
import Cubical.Categories.Displayed.Limits.CartesianClosedV as Path
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Presheaves.Cartesian
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
open import Cubical.Categories.Presheaf.StrictHom
open import Cubical.Categories.Presheaf.StrictHom.RightAdjoint
open import Cubical.Categories.Profunctor.StrictHom.Base
open import Cubical.Categories.Profunctor.StrictHom.Constructions.Extension
open import Cubical.Categories.Presheaf.Constructions.RightAdjoint
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Bifunctor

open Category
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
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
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
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.nat
    S3@(S , Sᴰ , .(α ⋆PshHomStrict β)) R3@(R , Rᴰ , β) α3@(α , αᴰ , Eq.refl) p ._ Eq.refl =
    Eq.pathToEq (makePshHomPath refl) -- this refl could use an annotation

  -- Quantifiers
  module _ {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} where
    /π₁ : Functor (Cᴰ / (P ×Psh Q)) (Cᴰ / P)
    /π₁ = (Idᴰ /Fⱽ π₁Eq P Q)

    ∀F : Functor (PRESHEAF (Cᴰ / P) ℓPᴰ) (PRESHEAF (Cᴰ / (P ×Psh Q)) ℓPᴰ)
    ∀F = reindPshFStrict /π₁

    ∀F-cocont : CoContinuous ∀F
    ∀F-cocont = reindPshFStrict-cocont /π₁

    module ∀Q = P⇒LargeStrict-cocontinuous ∀F ∀F-cocont

  PSHᴰ∀ : UniversalQuantifiers (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ)
    PSHIdL PSHAssoc PSHᴰFibration (PSHBP C ℓPSHᴰ) PSHπ₁NatEq PSH×aF-seq
  PSHᴰ∀ P Qᴰ .fst = ∀Q.P⇒Large Qᴰ
  PSHᴰ∀ P {Γ = Γ} Qᴰ .snd .PshIsoEq.isos R3@(R , Rᴰ , α) =
    PshHom Rᴰ (α *Strict PSHᴰ∀ P Qᴰ .fst)
      Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (∀Q.P⇒Large Qᴰ) ⟩
    PshHom (PshHomStrict→Eq α Push Rᴰ) (∀Q.P⇒Large Qᴰ)
      Iso⟨ PshHom≅PshHomStrict ⟩
    PshHomStrict (PshHomStrict→Eq α Push Rᴰ) (∀Q.P⇒Large Qᴰ)
      Iso⟨ ∀Q.P⇒Large-UMP Qᴰ (PshHomStrict→Eq α Push Rᴰ) ⟩
    PshHomStrict (∀F ⟅ PshHomStrict→Eq α Push Rᴰ ⟆) Qᴰ
      Iso⟨ invIso PshHom≅PshHomStrict ⟩
    PshHom (π₁Eq Γ P * (PshHomStrict→Eq α Push Rᴰ)) Qᴰ
      Iso⟨ precomp⋆PshHom-Iso $ BeckChevalley α Rᴰ ⟩
    PshHom
     (PshHomStrict→Eq (×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P))
       Push π₁ R P
       *Strict Rᴰ)
     Qᴰ

      Iso⟨ invIso (Push⊣* (PshHomStrict→Eq
         (×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P)))
           (π₁ R P *Strict Rᴰ) Qᴰ) ⟩
    PshHom (π₁ R _ *Strict Rᴰ)
           (×PshIntroStrict (π₁ R _ ⋆PshHomStrict α) (π₂ R _) *Strict Qᴰ)
    ∎Iso
    where
    module Γ = PresheafNotation Γ
    module α*Rᴰ = PresheafᴰNotation (PshHomStrict→Eq α Push Rᴰ)
    module Rᴰ = PresheafᴰNotation Rᴰ
  PSHᴰ∀ P Qᴰ .snd .PshIsoEq.nat
    S3@(S , Sᴰ , γ) R3@(R , Rᴰ , β) α3@(α , αᴰ , Eq.refl) p _ Eq.refl =
    -- This refl is very slow, can we get an annotation?
      Eq.pathToEq $ makePshHomPath refl
    where module Qᴰ = PresheafᴰNotation Qᴰ

  isCartesianClosedⱽPSHᴰ : isCartesianClosedⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL
    (PSHBP C ℓPSHᴰ) PSHπ₁NatEq PSH×aF-seq
  isCartesianClosedⱽPSHᴰ .fst = isCartesianⱽPSHᴰ
  isCartesianClosedⱽPSHᴰ .snd .fst = PSHᴰExponentials
  isCartesianClosedⱽPSHᴰ .snd .snd = PSHᴰ∀

  CCCⱽPSHᴰ : Path.CartesianClosedCategoryⱽ (Cartesian-PRESHEAF C ℓPSHᴰ) _ _
  CCCⱽPSHᴰ = EqCCCⱽ→CCCⱽ (Cartesian-PRESHEAF C ℓPSHᴰ) PSHAssoc PSHIdL PSHπ₁NatEq PSH×aF-seq
    (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) isCartesianClosedⱽPSHᴰ
