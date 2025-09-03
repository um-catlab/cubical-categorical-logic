{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Equiv.Dependent

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
  renaming (π to Reindexπ; reindex to CatReindex)
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Section

open Bifunctorᴰ
open Functorᴰ
open isIsoOver
open PshHomᴰ
private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level

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

module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  where
  -- This is like PshProdⱽ .F-hom but for homomorphisms/isomorphisms
  -- between presheaves of different levels
  --
  -- We should see if we can get this for free using Lift
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Pᴰ' : Presheafᴰ P Cᴰ ℓPᴰ'}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {Qᴰ' : Presheafᴰ Q Cᴰ ℓQᴰ'}
    where
    module _ {α : PshHom P Q} where
      _×ⱽHom_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (βᴰ : PshHomᴰ α Pᴰ' Qᴰ')
        → PshHomᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽHom βᴰ) .N-obᴰ (p , p') = (αᴰ .N-obᴰ p) , (βᴰ .N-obᴰ p')
      (αᴰ ×ⱽHom βᴰ) .N-homᴰ = ΣPathP ((αᴰ .N-homᴰ) , (βᴰ .N-homᴰ))

    module _ {α : PshIso P Q} where
      _×ⱽIso_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (βᴰ : PshIsoᴰ α Pᴰ' Qᴰ')
        → PshIsoᴰ α (Pᴰ ×ⱽPsh Pᴰ') (Qᴰ ×ⱽPsh Qᴰ')
      (αᴰ ×ⱽIso βᴰ) .fst = (αᴰ .fst) ×ⱽHom (βᴰ .fst)
      (αᴰ ×ⱽIso βᴰ) .snd .inv _ (q , q') = (αᴰ .snd .inv _ q) , (βᴰ .snd .inv _ q')
      (αᴰ ×ⱽIso βᴰ) .snd .rightInv _ _ = ΣPathP ((αᴰ .snd .rightInv _ _) , (βᴰ .snd .rightInv _ _))
      (αᴰ ×ⱽIso βᴰ) .snd .leftInv _ _ = ΣPathP ((αᴰ .snd .leftInv _ _) , (βᴰ .snd .leftInv _ _))


module _ {C : Category ℓ ℓ'} {Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  open Functorᴰ
  open Bifunctor
  open Bifunctorᴰ
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshProdⱽ≡ᴰ :
    Pᴰ ×ᴰPsh Qᴰ ≡ reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ
  PshProdⱽ≡ᴰ = Functorᴰ≡
    (λ Aᴰ → funExt λ (p , q) → ΣPathPProp (λ _ → isPropIsSet) refl)
    λ fᴰ → funExt λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP $
      (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
      , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _)

  -- This one is only Eq.refl on objects, would need a corresponding eqToPshIsoⱽ' like reindF''
  PshProdⱽ≅ᴰ :
    PshIsoⱽ (Pᴰ ×ᴰPsh Qᴰ) (reind (π₁ P Q) Pᴰ ×ⱽPsh reind (π₂ P Q) Qᴰ)
  PshProdⱽ≅ᴰ .fst .N-obᴰ x = x
  PshProdⱽ≅ᴰ .fst .N-homᴰ =
    ΣPathP ( (Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)
           , (Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))
  PshProdⱽ≅ᴰ .snd .inv _ x = x
  PshProdⱽ≅ᴰ .snd .rightInv _ _ = refl
  PshProdⱽ≅ᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α β : PshHom P Q}(α≡β : α ≡ β) {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  reindPathIsoⱽ : PshIsoⱽ (reind α Qᴰ) (reind β Qᴰ)
  reindPathIsoⱽ .fst .PshHomᴰ.N-obᴰ = Qᴰ.reind (funExt⁻ (funExt⁻ (cong fst α≡β) _) _)
  reindPathIsoⱽ .fst .PshHomᴰ.N-homᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $
      (sym (Qᴰ.reind-filler _ _)
      ∙ sym (Qᴰ.reind-filler _ _)
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩)
      ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.inv q =
    Qᴰ.reind ((funExt⁻ (funExt⁻ (cong fst (sym α≡β)) _) _))
  reindPathIsoⱽ .snd .isIsoOver.rightInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _
  reindPathIsoⱽ .snd .isIsoOver.leftInv q qᴰ =
    Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _ ∙ Qᴰ.reind-filler _ _

-- Reindexing is compositional:
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  (α : PshHom P Q)(β : PshHom Q R) (Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ)
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ
  reind-seq : reind α (reind β Rᴰ) ≡ reind (α ⋆PshHom β) Rᴰ
  reind-seq = Functorᴰ≡ (λ _ → refl) λ fᴰ → funExt λ p → funExt λ rᴰ →
    Rᴰ.rectify $ Rᴰ.≡out $
      sym (Rᴰ.reind-filler _ _ ∙ Rᴰ.reind-filler _ _)
      ∙ Rᴰ.reind-filler _ _

  reind-seqIsoⱽ : PshIsoⱽ (reind α (reind β Rᴰ)) (reind (α ⋆PshHom β) Rᴰ)
  reind-seqIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-seqIsoⱽ .fst .PshHomᴰ.N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $
    sym (Rᴰ.reind-filler _ _ ∙ Rᴰ.reind-filler _ _) ∙ Rᴰ.reind-filler _ _
  reind-seqIsoⱽ .snd .isIsoOver.inv = λ a z → z
  reind-seqIsoⱽ .snd .isIsoOver.rightInv b q = refl
  reind-seqIsoⱽ .snd .isIsoOver.leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  reind-id : Pᴰ ≡ reind idPshHom Pᴰ
  reind-id = Functorᴰ≡ (λ _ → refl)
    (λ _ → funExt λ _ → funExt λ _ → Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _)

  reind-idIsoⱽ : PshIsoⱽ Pᴰ (reind idPshHom Pᴰ)
  reind-idIsoⱽ .fst .PshHomᴰ.N-obᴰ = λ z → z
  reind-idIsoⱽ .fst .PshHomᴰ.N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ Pᴰ.reind-filler _ _
  reind-idIsoⱽ .snd .isIsoOver.inv = λ a z → z
  reind-idIsoⱽ .snd .isIsoOver.rightInv b q = refl
  reind-idIsoⱽ .snd .isIsoOver.leftInv a p = refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshHom P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module P = PresheafNotation P
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ {c}(p : P.p[ c ]) where
    reindYo-seq : reindYo p (reind α Qᴰ) ≡ reindYo (α .fst _ p) Qᴰ
    reindYo-seq = reind-seq _ _ _
      ∙ cong₂ reind (yoRec-natural _ _ _) refl

    reindYo-seqIsoⱽ : PshIsoⱽ (reindYo p (reind α Qᴰ)) (reindYo (α .fst c p) Qᴰ)
    reindYo-seqIsoⱽ =
      reind-seqIsoⱽ _ _ _ ⋆PshIsoⱽ reindPathIsoⱽ (yoRec-natural _ _ _)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (α : PshIso P Q) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module Qᴰ = PresheafᴰNotation Qᴰ
  -- is this the universal property of reind?
  reindPshIsoPshIsoᴰ : PshIsoᴰ α (reind (α .fst) Qᴰ) Qᴰ
  reindPshIsoPshIsoᴰ = mkPshIsoᴰEquivOver α (reind (α .fst) Qᴰ) Qᴰ
    (record { N-obᴰ = λ z → z
            ; N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler _ _
            })
    (λ a → record { equiv-proof = strictContrFibers _ })

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}

  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    motive : ∀ ℓQᴰ → (Q : Presheaf C ℓP) (α : P ≡ Q) → Type _
    motive ℓQᴰ Q α = ∀ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
      → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .fst) Qᴰ) Qᴰ
  reindPathToPshIsoPathP :
    ∀ {Q : Presheaf C ℓP} (α : P ≡ Q)
    → (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    -- TODO: give this kind of PathP a name? it's the analogue of PshIsoᴰ for paths
    → PathP (λ i → Presheafᴰ (α i) Cᴰ ℓQᴰ) (reind (pathToPshIso α .fst) Qᴰ) Qᴰ
  -- If we have prove pathToPshIso is an Iso then we could apply reindPshIsoPshIsoᴰ here
  reindPathToPshIsoPathP =
    J (motive _) λ Qᴰ →
      subst (λ α → reind (α .fst) Qᴰ ≡ Qᴰ)
        (sym pathToPshIsoRefl)
        (sym $ reind-id _)

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

-- Does this belong here?
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (F : GlobalSection Cᴰ) where
  UnitPsh→UnitPshᴰ : PshSection F (UnitPshᴰ {P = UnitPsh {C = C}})
  UnitPsh→UnitPshᴰ .N-obᴰ _ = tt
  UnitPsh→UnitPshᴰ .N-homᴰ = refl


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
