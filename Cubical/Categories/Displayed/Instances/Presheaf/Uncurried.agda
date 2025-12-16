{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
-- open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.Fiber
-- open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Constructions.Curry
import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct as Curry
import Cubical.Categories.Displayed.Presheaf.Morphism as Curry
-- open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
  renaming (_[-][-,_] to _[-][-,_]Curry)
open import Cubical.Categories.Displayed.Instances.Isomorphism
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open Category
open Functor
open PshHom
open PshIso
open Categoryᴰ

private
  variable ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'}
  {ℓP : Level}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where

  module _ (P : Presheaf C ℓP) (ℓPᴰ : Level) where
    PRESHEAFⱽ : Category _ _
    PRESHEAFⱽ = PRESHEAF (Cᴰ / P) ℓPᴰ

module _ {C : Category ℓC ℓC'} {ℓP ℓPᴰ : Level}
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = CategoryNotation PSH
    module PSHⱽ {P : Presheaf C ℓP} = CategoryNotation (PRESHEAFⱽ Cᴰ P ℓPᴰ)

  PSHISOⱽHom→PshIsoⱽ : ∀ {P} {Pᴰ Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ}  →
     PSHⱽ.ISOC [ Pᴰ , Qᴰ ] → PshIsoⱽ Pᴰ Qᴰ
  PSHISOⱽHom→PshIsoⱽ αᴰ .trans = αᴰ .fst
  PSHISOⱽHom→PshIsoⱽ αᴰ .nIso x .fst = αᴰ .snd .isIso.inv .N-ob x
  PSHISOⱽHom→PshIsoⱽ αᴰ .nIso x .snd .fst y i =
    αᴰ .snd .isIso.sec i .N-ob x y
  PSHISOⱽHom→PshIsoⱽ αᴰ .nIso x .snd .snd y i =
    αᴰ .snd .isIso.ret i .N-ob x y

  PshIsoⱽ→PSHISOⱽHom : ∀ {P} {Pᴰ Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ}  →
     PshIsoⱽ Pᴰ Qᴰ → PSHⱽ.ISOC [ Pᴰ , Qᴰ ]
  PshIsoⱽ→PSHISOⱽHom αᴰ .fst = αᴰ .trans
  PshIsoⱽ→PSHISOⱽHom αᴰ .snd .isIso.inv = invPshIso αᴰ .trans
  PshIsoⱽ→PSHISOⱽHom αᴰ .snd .isIso.sec = PshIso→rightInv αᴰ
  PshIsoⱽ→PSHISOⱽHom αᴰ .snd .isIso.ret = PshIso→leftInv αᴰ

module _
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = CategoryNotation PSH
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰ_
  PRESHEAFᴰ .⋆IdLᴰ {f = α} {yᴰ = Qᴰ} αᴰ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl)
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
  PRESHEAFᴰ .⋆IdRᴰ {yᴰ = Qᴰ} _ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Qᴰ.rectify {e = refl} refl)
    where
    module Qᴰ = PresheafᴰNotation Cᴰ _ Qᴰ
  PRESHEAFᴰ .⋆Assocᴰ {wᴰ = Rᴰ} _ _ _ =
    makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ → Rᴰ.rectify {e = refl} refl)
    where
    module Rᴰ = PresheafᴰNotation Cᴰ _ Rᴰ
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHom _ _

  private
    PSHᴰ = PRESHEAFᴰ
    module PSHᴰ = Fibers PRESHEAFᴰ
    PSHⱽ : ∀ {P} → Category _ _
    PSHⱽ {P} = PSHᴰ.v[ P ]
    -- PSHⱽ {ℓ} {ℓ'} {Qᴰ} = PRESHEAFⱽ {ℓP = ℓ} PRESHEAFᴰ Qᴰ ℓ'
    -- PSHⱽ : ∀ {ℓ} {ℓ'} {Qᴰ} → Category _ _
    -- PSHⱽ {ℓ} {ℓ'} {Qᴰ} = PRESHEAFⱽ {ℓP = ℓ} PRESHEAFᴰ Qᴰ ℓ'
  --   module PSHⱽ {ℓ} {ℓ'} {Qᴰ} = CategoryNotation (PSHⱽ {ℓ} {ℓ'} {Qᴰ})
  --   module PSHISOᴰ = Fibers (ISOᴰ PRESHEAFᴰ)

  open CartesianClosedCategoryⱽ'
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ :
    CartesianClosedCategoryⱽ' (Cartesian-PRESHEAF C ℓP) _ _
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .CartesianClosedCatᴰ = PRESHEAFᴰ
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .termⱽ P .fst = Unit*Pshᴰ
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .termⱽ P .snd =
    PSHᴰ [-][-, Unit*Pshᴰ ]
      PshIso⟨ Isos→PshIso
               (λ _ → iso (λ _ → tt) (λ _ → pshhom (λ _ _ → tt*) (λ _ _ _ _ → refl))
                          (λ _ → refl) (λ _ → makePshHomPath refl))
               (λ _ _ _ _ → refl) ⟩
    UnitPsh
    ∎PshIso
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .bpⱽ Pᴰ Qᴰ .fst = Pᴰ ×ⱽPsh Qᴰ
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .bpⱽ {x = P} Pᴰ Qᴰ .snd =
    (PSHᴰ [-][-, Pᴰ ×ⱽPsh Qᴰ ])
      PshIso⟨ Isos→PshIso
        (λ (R , Rᴰ , α) →
          PshHomᴰ α Rᴰ (Pᴰ ×ⱽPsh Qᴰ)
            Iso⟨ PshIso→Isos (PshIso→PshHomPshIso (reindPsh× (Idᴰ /Fⱽ α) Pᴰ Qᴰ)) Rᴰ ⟩
          PshHomⱽ Rᴰ (reindPshᴰNatTrans α Pᴰ ×Psh reindPshᴰNatTrans α Qᴰ)
            Iso⟨ ×Psh-UMP (reindPshᴰNatTrans α Pᴰ) (reindPshᴰNatTrans α Qᴰ) ⟩
          (PshHomᴰ α Rᴰ Pᴰ) × (PshHomᴰ α Rᴰ Qᴰ)
          ∎Iso)
        (λ _ _ _ _ → ΣPathP (makePshHomPath refl , makePshHomPath refl)) ⟩
    (PSHᴰ [-][-, Pᴰ ]) ×ⱽPsh (PSHᴰ [-][-, Qᴰ ])
    ∎PshIso
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .cartesianLifts {x = P} Pᴰ Q α .fst =
    reindPshᴰNatTrans α Pᴰ
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .cartesianLifts {x = P} Pᴰ Q α .snd =
    PSHᴰ [-][-, reindPshᴰNatTrans α Pᴰ ]
      PshIso⟨
        invPshIso
        (Isos→PshIso
          (λ (R , Rᴰ , β) →
            PshHomᴰ (β ⋆PshHom α) Rᴰ Pᴰ
              Iso⟨ PshIso→Isos (PshIso→PshHomPshIso (reindPshᴰNatTrans-seq β α Pᴰ)) Rᴰ ⟩
            PshHomᴰ β Rᴰ (reindPshᴰNatTrans α Pᴰ)
            ∎Iso
          )
          (λ (S , Sᴰ , β) (R , Rᴰ , γ) (η , ηᴰ , ηγ≡β) p →
            makePshHomᴰPathP _ _ _ (funExt₂ λ _ _ →
              Pᴰ.rectify $ Pᴰ.≡out $
                 {!!}
                 ∙ {!!}
            )
          ))
          ⟩
    reindPshᴰNatTrans (yoRec _ α) (PSHᴰ [-][-, Pᴰ ])
    ∎PshIso

     where
     module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
    --  module α*Pᴰ = PresheafᴰNotation Cᴰ Q (reindPshᴰNatTrans α Pᴰ)

  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .expⱽ = {!!}
  CartesianClosedCategoryⱽ'-PRESHEAFᴰ .∀s = {!!}

         -- ⟩→

  -- CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .fst {x = P} Pᴰ Q α .fst =
  --   reindPshᴰNatTrans α Pᴰ
  -- CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .fst {x = P} Pᴰ Q α .snd =
  --                )
  --     {!!}
  --     where
  --     module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
  -- CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .snd = {!!}
