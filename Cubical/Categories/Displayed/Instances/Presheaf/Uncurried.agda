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
open import Cubical.Categories.Functor.Base
-- open import Cubical.Categories.NaturalTransformation
-- open import Cubical.Categories.Constructions.Fiber
-- open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Presheaf
-- open import Cubical.Categories.Instances.Sets
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
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
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

module _
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    module PSH = Category (PRESHEAF C ℓP)
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰ
  PRESHEAFᴰ .idᴰ = idPshHomᴰ
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰ_
  PRESHEAFᴰ .⋆IdLᴰ  {yᴰ = Qᴰ} _ =
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
    module PSHᴰ = Categoryᴰ PRESHEAFᴰ

  CartesianClosedⱽ-PRESHEAFᴰ : CartesianClosedCategoryⱽ (Cartesian-PRESHEAF C ℓP) _ _
  CartesianClosedⱽ-PRESHEAFᴰ .fst = PRESHEAFᴰ
  CartesianClosedⱽ-PRESHEAFᴰ .snd .fst P .fst = Unit*Pshᴰ
  CartesianClosedⱽ-PRESHEAFᴰ .snd .fst P .snd =
    Isos→PshIso
      (λ _ → iso (λ _ → tt) (λ _ → pshhom (λ _ _ → tt*) (λ _ _ _ _ → refl))
                 (λ _ → refl) (λ _ → makePshHomPath refl))
      (λ _ _ _ _ → refl)
  CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .fst Pᴰ Qᴰ .fst = Pᴰ ×ⱽPsh Qᴰ
  CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .fst Pᴰ Qᴰ .snd =
    Isos→PshIso
      (λ _ →
        iso (λ αᴰ → αᴰ ⋆PshHomⱽ reindPshHom _ (π₁ Pᴰ Qᴰ) ,
                    αᴰ ⋆PshHomⱽ reindPshHom _ (π₂ Pᴰ Qᴰ))
            (λ (αᴰ , βᴰ) → ×PshIntro αᴰ βᴰ
                           ⋆PshHomⱽ (invPshIso $
                                      reindPsh× _ Pᴰ Qᴰ) .trans)
            (λ (αᴰ , βᴰ) → ΣPathP ((makePshHomPath refl) , (makePshHomPath refl)))
            λ αᴰ → makePshHomPath refl)
        (λ _ _ _ _ → ΣPathP (makePshHomPath refl , makePshHomPath refl))
  CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .fst {x = P} Pᴰ Q α .fst =
    reindPshᴰNatTrans α Pᴰ
  CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .fst {x = P} Pᴰ Q α .snd =
    Isos→PshIso
      (λ x → iso (λ αᴰ → αᴰ ⋆PshHomⱽ invPshIso (reindPshᴰNatTrans-seq (x .snd .snd) α Pᴰ) .trans)
                 (λ αᴰ → αᴰ ⋆PshHomⱽ reindPshᴰNatTrans-seq _ α Pᴰ .trans)
                 (λ αᴰ → ⋆PshHomAssoc
                            αᴰ
                            (reindPshᴰNatTrans-seq _ α Pᴰ .trans)
                            (invPshIso (reindPshᴰNatTrans-seq _ α Pᴰ) .trans)
                         -- ∙ cong (αᴰ ⋆PshHomⱽ_)
                         --    (PshIso→leftInv (reindPshᴰNatTrans-seq (x .snd .snd) α Pᴰ))
                         -- ∙ makePshHomPath refl
                         ∙ {!!}
                         )
                 {!!}
                 -- (λ αᴰ → ⋆PshHomAssoc _ _ _
                 --         ∙ cong (αᴰ ⋆PshHomⱽ_)
                 --            (PshIso→rightInv (reindPshᴰNatTrans-seq (x .snd .snd) α Pᴰ))
                 --         ∙ makePshHomPath refl))
                 )
      {!!}
      where
      module Pᴰ = PresheafᴰNotation Cᴰ P Pᴰ
  CartesianClosedⱽ-PRESHEAFᴰ .snd .snd .snd .snd = {!!}
