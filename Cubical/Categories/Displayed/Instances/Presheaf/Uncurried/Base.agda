{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Presheaf.Uncurried.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Functions.FunExtEquiv

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functor.Compose
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV


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
    PSH = PRESHEAF C ℓP
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

  isFibrationPRESHEAFᴰPointwise :
    ∀ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Q : Presheaf C ℓP) (α : PshHom Q P) →
    PointwiseIso {P = PRESHEAFᴰ [-][-, reindPshᴰNatTrans α Pᴰ ]}
      {Q = reindPsh (Idᴰ /Fⱽ yoRec (PRESHEAF C ℓP [-, P ]) α) (PRESHEAFᴰ [-][-, Pᴰ ])}
  isFibrationPRESHEAFᴰPointwise {P = P} Pᴰ Q α Rs@(R , Rᴰ , β) =
    PshHomⱽ Rᴰ (reindPshᴰNatTrans β (reindPshᴰNatTrans α Pᴰ))
      Iso⟨ invIso $ PshIso→Isos (PshIso→PshHomPshIso ((reindPshᴰNatTrans-seq β α Pᴰ))) Rᴰ ⟩
    PshHomⱽ Rᴰ (reindPshᴰNatTrans (β ⋆PshHom α) Pᴰ)
    ∎Iso

  isFibrationPRESHEAFᴰnatural :
    ∀ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Q : Presheaf C ℓP) (α : PshHom Q P) →
    PointwiseIsoNat (isFibrationPRESHEAFᴰPointwise Pᴰ Q α)
  isFibrationPRESHEAFᴰnatural {P = P} Pᴰ Q α
    Rs@(R , Rᴰ , β) Ss@(S , Sᴰ , γ) δs@(δ , δᴰ , δ≡) ϕᴰ =
      PSHᴰ.rectifyOut $
        {!!}
        ∙ PSHᴰ.reind-filler _

  isFibrationPRESHEAFᴰ : isFibration PRESHEAFᴰ
  isFibrationPRESHEAFᴰ {x = P} Pᴰ Q α .fst = reindPshᴰNatTrans α Pᴰ
  isFibrationPRESHEAFᴰ {x = P} Pᴰ Q α .snd =
    Isos→PshIso
      (isFibrationPRESHEAFᴰPointwise Pᴰ Q α)
      (isFibrationPRESHEAFᴰnatural Pᴰ Q α)
