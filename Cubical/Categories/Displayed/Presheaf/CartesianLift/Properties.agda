{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.CartesianLift.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Presheaf.CartesianLift.Base as CL
import Cubical.Categories.Displayed.Presheaf.CartesianLift.Manual as ManualCL

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ
open PshHom

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP}
         where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P

  module _ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    (cL : CartesianLift p Pᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module p*Pᴰ = PresheafⱽNotation (reindYo p Pᴰ)
      module cL = UniversalElementⱽ cL
    open ManualCL.CartesianLift
    CartesianLift→ManualCartesianLift : ManualCL.CartesianLift p Pᴰ
    CartesianLift→ManualCartesianLift .p*Pᴰ = cL.vertexⱽ
    CartesianLift→ManualCartesianLift .π =
      Pᴰ.reind (funExt⁻ (P .F-id) p) $ cL.elementⱽ
    CartesianLift→ManualCartesianLift .isCartesian .fst pᴰ =
      cL.introᴰ pᴰ
    CartesianLift→ManualCartesianLift .isCartesian .snd .fst pᴰ =
      Pᴰ.rectify $ Pᴰ.≡out $
        Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
        ∙ Pᴰ.reind-filler _ _
        ∙ Pᴰ.reind-filler _ _
        ∙ Pᴰ.≡in cL.βⱽ
    CartesianLift→ManualCartesianLift .isCartesian .snd .snd pᴰ =
      cong (cL.universalⱽ .fst)
        (Pᴰ.rectify $ Pᴰ.≡out $
          Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.reind-filler _ _ ⟩
          ∙ Pᴰ.reind-filler _ _
          ∙ Pᴰ.reind-filler _ _
        ) ∙
      cL.universalⱽ .snd .snd pᴰ

  module _ {x} (p : P.p[ x ]) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    (McL : ManualCL.CartesianLift p Pᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module McL = ManualCL.CartesianLift McL
      module p*Pᴰ = PresheafⱽNotation (reindYo p Pᴰ)
    open UniversalElementⱽ
    ManualCartesianLift→CartesianLift : CL.CartesianLift p Pᴰ
    ManualCartesianLift→CartesianLift .vertexⱽ = McL.p*Pᴰ
    ManualCartesianLift→CartesianLift .elementⱽ = Cᴰ.idᴰ Pᴰ.⋆ᴰ McL.π
    ManualCartesianLift→CartesianLift .universalⱽ .fst = McL.isCartesian .fst
    ManualCartesianLift→CartesianLift .universalⱽ {y} {yᴰ} {f} .snd =
      subst
        motive
        (funExt (λ fᴰ → Pᴰ.rectify $ Pᴰ.≡out $
          Pᴰ.⟨⟩⋆⟨ sym $ Pᴰ.⋆IdL _ ⟩ ∙ Pᴰ.reind-filler _ _ ∙ Pᴰ.reind-filler _ _))
        (McL.isCartesian .snd)
      where
        motive : (Cᴰ [ f ][ yᴰ , McL.p*Pᴰ ] → Pᴰ.p[ f P.⋆ p ][ yᴰ ]) → Type _
        motive introⱽ = section introⱽ (McL.isCartesian .fst) × retract introⱽ (McL.isCartesian .fst)

open ManualCL.CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
         where
  private
    module P = PresheafNotation P
  isFibrationManual→isFibration : ManualCL.isFibration Pᴰ → CL.isFibration Pᴰ
  isFibrationManual→isFibration isFib p =
    ManualCartesianLift→CartesianLift p Pᴰ (isFib p)

  isFibration→isFibrationManual : CL.isFibration Pᴰ → ManualCL.isFibration Pᴰ
  isFibration→isFibrationManual isFib p =
    CartesianLift→ManualCartesianLift p Pᴰ (isFib p)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (F : Functor C D)
         where
  -- TODO This can probably be proven directly for
  -- CL.isFibration without going through the manual construction
  module _ {P : Presheaf D ℓP}
    (Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ) (isFibPᴰ : isFibration Pᴰ) where
    isFibrationReindFunc : isFibration (reindFunc F Pᴰ)
    isFibrationReindFunc =
      isFibrationManual→isFibration (reindFunc F Pᴰ)
        (ManualCL.isFibrationReindFunc F Pᴰ
          (isFibration→isFibrationManual Pᴰ isFibPᴰ))
module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  (α : PshHet F P Q){Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  (isFibQᴰ : isFibration Qᴰ)
  where
  -- TODO This can probably be proven directly for
  -- CL.isFibration without going through the manual construction
  isFibrationReindHet : isFibration (reindHet α Qᴰ)
  isFibrationReindHet =
      isFibrationManual→isFibration (reindHet α Qᴰ)
        (ManualCL.isFibrationReindHet α
          (isFibration→isFibrationManual Qᴰ isFibQᴰ))
