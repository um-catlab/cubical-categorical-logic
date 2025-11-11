{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.General where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Exponentials.Small
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Functor
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Limits.CartesianV
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Reindex
open import Cubical.Categories.Displayed.Presheaf.Constructions.Lift
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit
open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Constructions.Exponential

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level
  variable ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓEᴰ ℓEᴰ' : Level

open Category
open Categoryᴰ
-- TODO: move these upstream
PRESHEAF : (C : Category ℓC ℓC') (ℓP : Level) → Category _ _
PRESHEAF C ℓP .ob = Presheaf C ℓP
PRESHEAF C ℓP .Hom[_,_] = PshHom
PRESHEAF C ℓP .id = idPshHom
PRESHEAF C ℓP ._⋆_ = _⋆PshHom_
PRESHEAF C ℓP .⋆IdL = λ f → makePshHomPath refl
PRESHEAF C ℓP .⋆IdR = λ f → makePshHomPath refl
PRESHEAF C ℓP .⋆Assoc = ⋆PshHomAssoc
PRESHEAF C ℓP .isSetHom = isSetPshHom _ _

-- TODO: move upstream
PRESHEAFᴰ' : {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ (ℓP ℓPᴰ : Level) → Categoryᴰ (PRESHEAF C ℓP) _ _
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .Hom[_][_,_] α Pᴰ Qᴰ = PshHomᴰ α Pᴰ Qᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .idᴰ = idPshHomᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ ._⋆ᴰ_ = _⋆PshHomᴰ_
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .⋆IdLᴰ {P}{Q}{α}{Pᴰ}{Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ (funExt (λ p → Qᴰ.rectify (Qᴰ.≡out refl)))
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .⋆IdRᴰ {P}{Q}{α}{Pᴰ}{Qᴰ} αᴰ = makePshHomᴰPathP _ _ _ (funExt (λ p → Qᴰ.rectify (Qᴰ.≡out refl)))
  where module Qᴰ = PresheafᴰNotation Qᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .⋆Assocᴰ {wᴰ = Sᴰ} αᴰ βᴰ γᴰ = makePshHomᴰPathP _ _ _ (funExt (λ p → Sᴰ.rectify (Sᴰ.≡out refl)))
  where module Sᴰ = PresheafᴰNotation Sᴰ
PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ .isSetHomᴰ = isSetPshHomᴰ _ _ _

module _ {ℓP ℓQ ℓPᴰ ℓQᴰ ℓRᴰ ℓSᴰ}{C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}{Sᴰ : Presheafᴰ Q Cᴰ ℓSᴰ}
  {α : PshHom P Q} where
  ⋆PshHomAssocᴰⱽⱽ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ)(γᴰ : PshHomⱽ Rᴰ Sᴰ)
    → (αᴰ ⋆PshHomᴰⱽ βᴰ) ⋆PshHomᴰⱽ γᴰ ≡ αᴰ ⋆PshHomᴰⱽ (βᴰ ⋆PshHomⱽ γᴰ)
  ⋆PshHomAssocᴰⱽⱽ αᴰ βᴰ γᴰ = makePshHomᴰPath refl

module _ {ℓP ℓQ ℓPᴰ ℓQᴰ}{C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  ⋆PshHomIdRᴰⱽ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) → αᴰ ⋆PshHomᴰⱽ idPshHomᴰ ≡ αᴰ
  ⋆PshHomIdRᴰⱽ αᴰ = makePshHomᴰPath refl

module _ {ℓP ℓQ ℓPᴰ ℓQᴰ ℓRᴰ}{C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  postcomp⋆PshHomᴰⱽ-Iso
    : (βⱽ : PshIsoⱽ Qᴰ Rᴰ)
    → ∀ {α : PshHom P Q}
    → Iso (PshHomᴰ α Pᴰ Qᴰ) (PshHomᴰ α Pᴰ Rᴰ)
  postcomp⋆PshHomᴰⱽ-Iso βⱽ .Iso.fun = _⋆PshHomᴰⱽ βⱽ .fst
  postcomp⋆PshHomᴰⱽ-Iso βⱽ .Iso.inv = _⋆PshHomᴰⱽ invPshIsoⱽ βⱽ .fst
  postcomp⋆PshHomᴰⱽ-Iso βⱽ .Iso.rightInv αᴰ =
    ⋆PshHomAssocᴰⱽⱽ _ _ _
    ∙ cong (αᴰ ⋆PshHomᴰⱽ_) (PshIsoⱽ→PshIsoⱽ' _ _ βⱽ .snd .snd .snd)
    ∙ ⋆PshHomIdRᴰⱽ αᴰ
  postcomp⋆PshHomᴰⱽ-Iso βⱽ .Iso.leftInv αᴰ = ⋆PshHomAssocᴰⱽⱽ _ _ _
    ∙ cong (αᴰ ⋆PshHomᴰⱽ_) (PshIsoⱽ→PshIsoⱽ' _ _ βⱽ .snd .snd .fst)
    ∙ ⋆PshHomIdRᴰⱽ αᴰ

open Iso
open UniversalElementⱽ
module _ (C : Category ℓC ℓC') (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (ℓP ℓPᴰ : Level) where
  private
    module PSHᴰ = Fibers (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ)

  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓP}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Rᴰ = PresheafᴰNotation Rᴰ
    module _ {α : PshHom P Q} where
      ⋆PshHomᴰⱽ≡ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ)
        → αᴰ ⋆PshHomᴰⱽ βᴰ ≡ (αᴰ PSHᴰ.⋆ᴰⱽ βᴰ)
      ⋆PshHomᴰⱽ≡ αᴰ βᴰ = sym (fromPathP (makePshHomᴰPathP (αᴰ PSHᴰ.⋆ᴰ βᴰ) (αᴰ ⋆PshHomᴰⱽ βᴰ) _
        (funExt λ pᴰ → Rᴰ.rectify $ Rᴰ.≡out refl)))
  module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓP}{R : Presheaf C ℓP}
    (α : PshHom Q P)(β : PshHom R Q)(Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Rᴰ : Presheafᴰ R Cᴰ ℓPᴰ)(βᴰ : PshHomᴰ β Rᴰ (reind α Pᴰ))
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module α*Pᴰ = PresheafⱽNotation
        (reindYo {C = PRESHEAF C _}{Cᴰ = PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ} α (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ [-][-, Pᴰ ]))

    reind⋆ᴰ≡⋆PshHomᴰ : βᴰ α*Pᴰ.⋆ᴰ (idPshHomᴰ ⋆PshHomᴰ reind-π) ≡ (βᴰ ⋆PshHomᴰ idPshHomᴰ) ⋆PshHomᴰ reind-π
    reind⋆ᴰ≡⋆PshHomᴰ = fromPathP (makePshHomᴰPathP _ _ _ (funExt λ rᴰ → Pᴰ.rectify $ Pᴰ.≡out $ refl ))

    reind⋆ᴰⱽ≡⋆PshHomᴰ : βᴰ α*Pᴰ.⋆ᴰⱽ (idPshHomᴰ ⋆PshHomᴰ reind-π) ≡ (βᴰ ⋆PshHomᴰⱽ idPshHomᴰ) ⋆PshHomᴰ reind-π
    reind⋆ᴰⱽ≡⋆PshHomᴰ = fromPathP (reind⋆ᴰ≡⋆PshHomᴰ ◁ (makePshHomᴰPathP _ _ _ (funExt λ rᴰ → Pᴰ.rectify $ Pᴰ.≡out $
      refl)))

  module _ {P : Presheaf C ℓP}{R : Presheaf C ℓP}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓPᴰ}
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Rᴰ = PresheafᴰNotation Rᴰ
    module _ {β : PshHom P R} where
      ⋆PshHomⱽᴰ≡ : (αⱽ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ)
        → αⱽ ⋆PshHomⱽᴰ βᴰ ≡ (αⱽ PSHᴰ.⋆ⱽᴰ βᴰ)
      ⋆PshHomⱽᴰ≡ αⱽ βᴰ = sym (fromPathP (makePshHomᴰPathP (αⱽ PSHᴰ.⋆ᴰ βᴰ) (αⱽ ⋆PshHomⱽᴰ βᴰ) _
        (funExt λ pᴰ → Rᴰ.rectify $ Rᴰ.≡out refl)))

  -- TODO: need Iso (PshHomᴰ α) (NatTransᴰ (PH→NT α)) and vice-versa
  PRESHEAFᴰ-Terminalsⱽ : Terminalsⱽ (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ)
  PRESHEAFᴰ-Terminalsⱽ P .vertexⱽ = LiftPshᴰ UnitPshᴰ ℓPᴰ
  PRESHEAFᴰ-Terminalsⱽ P .elementⱽ = _
  PRESHEAFᴰ-Terminalsⱽ P .universalⱽ .fst _ = UnitPshᴰ-introᴰ ⋆PshHomᴰⱽ LiftHomⱽ UnitPshᴰ
  PRESHEAFᴰ-Terminalsⱽ P .universalⱽ .snd .fst = λ _ → refl
  PRESHEAFᴰ-Terminalsⱽ P .universalⱽ .snd .snd = λ αᴰ →
    isoFunInjective (postcomp⋆PshHomᴰⱽ-Iso (invPshIsoⱽ (LiftIsoⱽ UnitPshᴰ))) _ _ (isoInvInjective UnitPshᴰ-UMP _ _ refl)

  PRESHEAFᴰ-BinProductsⱽ : BinProductsⱽ (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ)
  PRESHEAFᴰ-BinProductsⱽ P Pᴰ,Qᴰ .vertexⱽ = Pᴰ,Qᴰ .fst ×ⱽPsh Pᴰ,Qᴰ .snd
  PRESHEAFᴰ-BinProductsⱽ P Pᴰ,Qᴰ .elementⱽ =
    ×ⱽ-π₁ {Pᴰ = Pᴰ,Qᴰ .fst}{Qᴰ = Pᴰ,Qᴰ .snd}
    , ×ⱽ-π₂ {Pᴰ = Pᴰ,Qᴰ .fst}{Qᴰ = Pᴰ,Qᴰ .snd}
  PRESHEAFᴰ-BinProductsⱽ P Pᴰ,Qᴰ .universalⱽ .fst αᴰβᴰ =
    ×ⱽ-introᴰ (αᴰβᴰ .fst) (αᴰβᴰ .snd)
  PRESHEAFᴰ-BinProductsⱽ P Pᴰ,Qᴰ .universalⱽ .snd .fst αᴰβᴰ =
  -- TODO: figure out how to make this faster
    ΣPathP (sym (⋆PshHomᴰⱽ≡ (×ⱽ-introᴰ (αᴰβᴰ .fst) (αᴰβᴰ .snd)) (×ⱽ-π₁ {Pᴰ = Pᴰ,Qᴰ .fst}{Qᴰ = Pᴰ,Qᴰ .snd})) ∙ (cong fst $ ×ⱽPsh-UMPᴰ {Qᴰ = Pᴰ,Qᴰ .fst}{Rᴰ = Pᴰ,Qᴰ .snd} .leftInv (αᴰβᴰ .fst , αᴰβᴰ .snd))
    , sym (⋆PshHomᴰⱽ≡ (×ⱽ-introᴰ (αᴰβᴰ .fst) (αᴰβᴰ .snd)) (×ⱽ-π₂ {Pᴰ = Pᴰ,Qᴰ .fst}{Qᴰ = Pᴰ,Qᴰ .snd})) ∙ (cong snd $ ×ⱽPsh-UMPᴰ {Qᴰ = Pᴰ,Qᴰ .fst}{Rᴰ = Pᴰ,Qᴰ .snd} .leftInv (αᴰβᴰ .fst , αᴰβᴰ .snd) ))
  PRESHEAFᴰ-BinProductsⱽ P Pᴰ,Qᴰ .universalⱽ .snd .snd αᴰ =
    isoFun≡ (×ⱽPsh-UMPᴰ {Qᴰ = Pᴰ,Qᴰ .fst} {Rᴰ = Pᴰ,Qᴰ .snd})
      (ΣPathP ((sym (⋆PshHomᴰⱽ≡ αᴰ _)) , (sym (⋆PshHomᴰⱽ≡ αᴰ _))))

  PRESHEAFᴰ-isFibration : isFibration (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ)
  PRESHEAFᴰ-isFibration {P} Pᴰ {Q} α .vertexⱽ = reind α Pᴰ
  PRESHEAFᴰ-isFibration {P} Pᴰ {Q} α .elementⱽ = idPshHomᴰ ⋆PshHomᴰ reind-π
  PRESHEAFᴰ-isFibration {P} Pᴰ {Q} α .universalⱽ {R} {Rᴰ} {β} .fst = reind-introᴰ
  PRESHEAFᴰ-isFibration {P} Pᴰ {Q} α .universalⱽ {R} {Rᴰ} {β} .snd =
    (λ βαᴰ →
     (reind-introᴰ βαᴰ α*Pᴰ.⋆ᴰⱽ (idPshHomᴰ ⋆PshHomᴰ reind-π))
       ≡⟨ lem (reind-introᴰ βαᴰ) ⟩
     (reind-introᴰ βαᴰ ⋆PshHomᴰ reind-π)
       ≡⟨ reind-UMP {α = β}{β = α} .leftInv βαᴰ ⟩
     βαᴰ ∎)
    , (λ βᴰ →
      cong reind-introᴰ (lem βᴰ)
      ∙ reind-UMP .rightInv βᴰ)
    where
      module α*Pᴰ = PresheafⱽNotation
        (reindYo {C = PRESHEAF C _}{Cᴰ = PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ} α (PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ [-][-, Pᴰ ]))
      module Pᴰ = PresheafᴰNotation Pᴰ

      lem : ∀ (βᴰ : PshHomᴰ β Rᴰ (reind α Pᴰ))
        → (βᴰ α*Pᴰ.⋆ᴰⱽ (idPshHomᴰ ⋆PshHomᴰ reind-π))
          ≡ βᴰ ⋆PshHomᴰ reind-π
      lem βᴰ = reind⋆ᴰⱽ≡⋆PshHomᴰ _ _ _ _ _
        ∙ cong (_⋆PshHomᴰ reind-π) (⋆PshHomIdRᴰⱽ βᴰ)

  PRESHEAFᴰ-CCⱽ : CartesianCategoryⱽ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ-CCⱽ .CartesianCategoryⱽ.Cᴰ = PRESHEAFᴰ' Cᴰ ℓP ℓPᴰ
  PRESHEAFᴰ-CCⱽ .CartesianCategoryⱽ.termⱽ = PRESHEAFᴰ-Terminalsⱽ
  PRESHEAFᴰ-CCⱽ .CartesianCategoryⱽ.bpⱽ = PRESHEAFᴰ-BinProductsⱽ
  PRESHEAFᴰ-CCⱽ .CartesianCategoryⱽ.cartesianLifts = PRESHEAFᴰ-isFibration

-- For exponentials need to implement ⇒PshLargeⱽ
--   PRESHEAFᴰ-Exponentialsⱽ : Exponentialsⱽ (PRESHEAFᴰ Cᴰ ℓS ℓS') {!!} {!!}
--   PRESHEAFᴰ-Exponentialsⱽ = {!!}
