{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Profunctor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function


open import Cubical.Categories.Category
import Cubical.Categories.Instances.TotalCategory as TotalCat
import Cubical.Categories.Instances.TotalCategory.More as TotalCat
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Presheaf.Base
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Instances.Functor

private
  variable
    ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓS : Level
    ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓSᴰ : Level

Profunctorᴰ : {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  → Profunctor C D ℓS
  → (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  → ∀ ℓSᴰ → Type _
Profunctorᴰ P Cᴰ Dᴰ ℓSᴰ = Functorᴰ P Cᴰ (PRESHEAFᴰ Dᴰ _ ℓSᴰ)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
         ℓS ℓSᴰ where
  PROFUNCTORᴰ : Categoryᴰ (PROFUNCTOR C D ℓS) _ _
  PROFUNCTORᴰ = FUNCTORᴰ Cᴰ (PRESHEAFᴰ Dᴰ ℓS ℓSᴰ)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {R : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (ues : UniversalElements R)
         (Rᴰ : Profunctorᴰ R Cᴰ Dᴰ ℓSᴰ)
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  UniversalElementsᴰ : Type _
  UniversalElementsᴰ = ∀ x (xᴰ : Cᴰ.ob[ x ])
    → UniversalElementᴰ _ (ues x) (Rᴰ.F-obᴰ xᴰ)

-- A vertical profunctor is a profunctor over Yoneda
Profunctorⱽ : {C : Category ℓC ℓC'}
  → (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → (Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ')
  → ∀ ℓSᴰ → Type _
Profunctorⱽ Cᴰ Dᴰ ℓSᴰ = Profunctorᴰ YO Cᴰ Dᴰ ℓSᴰ

module _ {C : Category ℓC ℓC'}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
         (Rᴰ : Profunctorⱽ Cᴰ Dᴰ ℓSᴰ)
         where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  UniversalElementsⱽ : Type _
  UniversalElementsⱽ = ∀ x (xᴰ : Cᴰ.ob[ x ]) →
    UniversalElementⱽ Dᴰ x (Rᴰ.F-obᴰ xᴰ)

module _ {C : Category ℓC ℓC'}
         {D : Category ℓD ℓD'}
         {R : Profunctor C D ℓS}
         {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
         {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
         (Rᴰ : Profunctorᴰ R Cᴰ Dᴰ ℓSᴰ)
         where
  ∫Prof : Profunctor (TotalCat.∫C Cᴰ) (TotalCat.∫C Dᴰ) (ℓ-max ℓS ℓSᴰ)
  ∫Prof =
    (postcomposeF _ ΣF)
    ∘F precomposeF _ TotalCat.∫C-op-commute
    ∘F ∫F-Functor (Dᴰ ^opᴰ) (SETᴰ ℓS ℓSᴰ)
    ∘F TotalCat.∫F Rᴰ

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Rᴰ = Functorᴰ Rᴰ
  open UniversalElement
  open UniversalElementᴰ
  ∫ues : ∀ {ues : UniversalElements R} → (uesᴰ : UniversalElementsᴰ ues Rᴰ)
    → UniversalElements ∫Prof
  ∫ues uesᴰ (x , xᴰ) = ∫ue (uesᴰ x xᴰ)


module _ (C : Category ℓC ℓC') (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  open Functorᴰ
  open NatTransᴰ
  PshHomᴰPshᴰ : ∀ {Q : Presheaf C ℓQ} (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    → Presheafᴰ (PshHomPsh Q) (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ) (ℓ-max
                                                      (ℓ-max (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') ℓQᴰ) ℓP) ℓPᴰ)
  PshHomᴰPshᴰ Qᴰ .F-obᴰ Pᴰ α = (PshHomᴰ α Pᴰ Qᴰ) , (isSetPshHomᴰ _ _ _)
  PshHomᴰPshᴰ Qᴰ .F-homᴰ αᴰ _ βᴰ = NatTransᴰ→PshHomᴰ αᴰ ⋆PshHomᴰ βᴰ
  PshHomᴰPshᴰ Qᴰ .F-idᴰ = funExt (λ q → funExt λ qᴰ → makePshHomᴰPathP _ _ _ (funExt (λ αᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl))) where
    module Qᴰ = PresheafᴰNotation Qᴰ
  PshHomᴰPshᴰ Qᴰ .F-seqᴰ αᴰ βᴰ = funExt (λ q → funExt λ qᴰ → makePshHomᴰPathP _ _ _ (funExt λ γᴰ →
    Qᴰ.rectify $ Qᴰ.≡out $ refl)) where
    module Qᴰ = PresheafᴰNotation Qᴰ

  PshHomᴰProfᴰ : Profunctorᴰ PshHomProf (PRESHEAFᴰ Cᴰ ℓP ℓPᴰ) (PRESHEAFᴰ Cᴰ ℓQ ℓQᴰ) _
  PshHomᴰProfᴰ .F-obᴰ Qᴰ = PshHomᴰPshᴰ Qᴰ
  PshHomᴰProfᴰ .F-homᴰ αᴰ .N-obᴰ Qᴰ β βᴰ = βᴰ ⋆PshHomᴰ NatTransᴰ→PshHomᴰ αᴰ
  PshHomᴰProfᴰ .F-homᴰ {P}{Q}{α}{Pᴰ}{Qᴰ} αᴰ .N-homᴰ {R}{S}{β}{Rᴰ}{Sᴰ} βᴰ = funExt λ γ → funExt λ γᴰ →
    makePshHomᴰPathP _ _ _ (funExt λ sᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
    where
      module Qᴰ = PresheafᴰNotation Qᴰ
  -- funExt (λ γ → funExt λ γᴰ → makePshHomᴰPathP _ _ _ (funExt (λ qᴰ → {!!})))
  PshHomᴰProfᴰ .F-idᴰ {P} {Pᴰ} = makeNatTransPathᴰ _ _ _ (implicitFunExt (funExt (λ Qᴰ → funExt (λ β → funExt λ βᴰ →
    makePshHomᴰPathP _ _ _ (funExt (λ qᴰ → Pᴰ.rectify $ Pᴰ.≡out $ refl)))))) where
      module Pᴰ = PresheafᴰNotation Pᴰ
  PshHomᴰProfᴰ .F-seqᴰ {P} {P'} {P''} {α} {α'} {Pᴰ} {Pᴰ'} {Pᴰ''} αᴰ αᴰ' = makeNatTransPathᴰ _ _ _ (implicitFunExt (funExt (λ Qᴰ → funExt (λ β → funExt λ βᴰ →
    makePshHomᴰPathP _ _ _ (funExt λ qᴰ → Pᴰ''.rectify $ Pᴰ''.≡out $ refl))))) where
      module Pᴰ'' = PresheafᴰNotation Pᴰ''

-- Neologism?
Prosection : {C : Category ℓC ℓC'}{D : Category ℓC ℓC'}
  → (F : Functor C D)
  → (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  → ∀ ℓSᴰ → Type _
Prosection F Dᴰ ℓSᴰ = Section F (PRESHEAFⱽ Dᴰ ℓSᴰ)

GlobalProsection : {C : Category ℓC ℓC'}
  → (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  → ∀ ℓSᴰ → Type _
GlobalProsection = Prosection Id
