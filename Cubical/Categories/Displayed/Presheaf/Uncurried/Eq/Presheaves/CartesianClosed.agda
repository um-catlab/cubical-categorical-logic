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

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base hiding (PshHomᴰ ; _⋆PshHomᴰ_ ; PRESHEAFᴰ)
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
  PSHᴰExponentials {x = P} Pᴰ Qᴰ .snd .PshIsoEq.nat
    S3@(S , Sᴰ , .(α ⋆PshHomStrict β)) R3@(R , Rᴰ , β) α3@(α , αᴰ , Eq.refl) p ._ Eq.refl =
    Eq.pathToEq (makePshHomPath refl)

  PSHᴰExponentials' : Exponentialsⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHIdL (BPⱽ+Fibration→AllLRⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHᴰBPⱽ PSHᴰFibration)
  PSHᴰExponentials' {x = P} Pᴰ Qᴰ .fst = Pᴰ ⇒PshLarge Qᴰ
  PSHᴰExponentials' {x = P} Pᴰ Qᴰ .snd =
    (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ [-][-, Pᴰ ⇒PshLarge Qᴰ ])
    -- PshHom[ R , α * (Pᴰ ⇒ Qᴰ) ]
      PshIsoEq⟨ PushF⊣* ⟩
    -- PshHom[ α Push R , Pᴰ ⇒ Qᴰ ]
    reindPsh PushF (PSHHOMCAT (Cᴰ / P) ℓPSHᴰ [-, Pᴰ ⇒PshLarge Qᴰ ])
      PshIsoEq⟨ {!!} ⟩
    -- PshHom[ (α Push R) ×ⱽ Pᴰ , Qᴰ ]
    {!!}
      PshIsoEq⟨ {!!} ⟩
    -- PshHom[ (α Push (R ×ⱽ (α * Pᴰ))) , Qᴰ ]
    {!!}
      PshIsoEq⟨ {!!} ⟩
    -- PshHom[ R ×ⱽ (α * Pᴰ) , α * Qᴰ ]
    {!!}
      PshIsoEq⟨ {!!} ⟩
    -- Definitional stuff
    reindPsh (LRⱽF (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc (λ f → Eq.refl) Pᴰ (BPⱽ+Fibration→AllLRⱽ (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHAssoc PSHᴰBPⱽ PSHᴰFibration Pᴰ)) (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ [-][-, Qᴰ ])
      ∎PshIsoEq

  ∀Pshᴰ : {P : Presheaf C ℓPSHᴰ}{Q : Presheaf C ℓPSHᴰ} → (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPSHᴰ) → Presheafᴰ P Cᴰ ℓPSHᴰ
  ∀Pshᴰ {P = P}{Q = Q} Pᴰ =
    reindPsh (reindPshFStrict (Idᴰ /Fⱽ π₁Eq P Q) ∘F YOStrict) ((PRESHEAF (Cᴰ / (P ×Psh Q)) _ [-, Pᴰ ]))

  PSHᴰ∀ : UniversalQuantifiers (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL PSHAssoc PSHᴰFibration PSHBP PSHπ₁NatEq PSH×aF-seq
  -- Pᴰ : Pshᴰ (P × Q)
  -- -----------------
  -- (∀Q Pᴰ) (Γ , Γᴰ , p) = PshHom ? Pᴰ
  PSHᴰ∀ Q {P} Pᴰ .fst = ∀Pshᴰ Pᴰ

  PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.isos (R , Rᴰ , α) =
    PshHom Rᴰ (α *Strict ∀Pshᴰ Pᴰ)
      Iso⟨ Push⊣* (PshHomStrict→Eq α) Rᴰ (∀Pshᴰ Pᴰ) ⟩
    PshHom (α PushStrict Rᴰ) (∀Pshᴰ Pᴰ)
      Iso⟨ invIso {!!} ⟩
    PshHom (π₁ P Q *Strict α PushStrict Rᴰ) Pᴰ
      -- Beck Chevalley
      Iso⟨ precomp⋆PshHom-Iso (BeckChevalley α Rᴰ) ⟩
    PshHom (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) PushStrict (π₁ R Q) *Strict Rᴰ) Pᴰ
      Iso⟨ invIso $ Push⊣* _ _ _ ⟩
    PshHom (π₁ R Q *Strict Rᴰ) (×PshIntroStrict (π₁ R Q ⋆PshHomStrict α) (π₂ R Q) *Strict Pᴰ)
      ∎Iso
  PSHᴰ∀ Q {P} Pᴰ .snd .PshIsoEq.nat = {!!}

  isCartesianClosedⱽPSHᴰ : isCartesianClosedⱽ PSHAssoc (PRESHEAFᴰ Cᴰ ℓPSHᴰ ℓPSHᴰ) PSHIdL  PSHBP PSHπ₁NatEq PSH×aF-seq
  isCartesianClosedⱽPSHᴰ .fst = isCartesianⱽPSHᴰ
  isCartesianClosedⱽPSHᴰ .snd .fst = PSHᴰExponentials
  isCartesianClosedⱽPSHᴰ .snd .snd = PSHᴰ∀
