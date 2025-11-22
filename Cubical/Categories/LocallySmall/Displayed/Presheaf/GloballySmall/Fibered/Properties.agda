{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.Fibered.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Functions.FunExtEquiv

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

import Cubical.Categories.Category.Base as SmallCat
import Cubical.Categories.Displayed.Base as SmallCatᴰ
import Cubical.Categories.Presheaf.Base as SmallPsh
import Cubical.Categories.Displayed.Presheaf.Base as SmallPshᴰ
import Cubical.Categories.Functor.Base as SmallFunctor
import Cubical.Categories.Displayed.Functor as SmallFunctorᴰ
import Cubical.Categories.Instances.Sets as SmallCatSets
import Cubical.Categories.Displayed.Instances.Sets as SmallCatᴰSetsᴰ
import Cubical.Categories.Constructions.Fiber as SmallCatFiber

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.Fibered
open import Cubical.Categories.LocallySmall.Presheaf.GloballySmall.Fibered.Base

open import Cubical.Categories.LocallySmall.Displayed.Category
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.Fibered.Base

open import Cubical.Categories.LocallySmall.Displayed.Presheaf.GloballySmall.Fibered.Base

open Σω
open Liftω

private
  module SET = CategoryᴰNotation SET
  module SETᴰ = SmallFibersᴰNotation SETᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓP : Level} (P : Presheaf C ℓP)
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
    P' = Presheaf→SmallPresheaf C ℓP P
    Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ
  SmallPresheafᴰ : Type _
  SmallPresheafᴰ = SmallPshᴰ.Presheafᴰ P' Cᴰ' ℓPᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓP : Level} (P : SmallPresheaf C ℓP)
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
    Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ
  SmallPresheafᴰOverSmallPresheaf : Type _
  SmallPresheafᴰOverSmallPresheaf = SmallPshᴰ.Presheafᴰ P Cᴰ' ℓPᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓP : Level} {P : SmallPresheaf C ℓP}
  {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
  {ℓPᴰ : Level}
  where
  open Functorᴰ
  private
    Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ
    module SFunctor = SmallFunctor.Functor
    module SFunctorᴰ = SmallFunctorᴰ.Functorᴰ
  SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ :
    SmallPresheafᴰOverSmallPresheaf P Cᴰ ℓPᴰ →
    SmallPresheafᴰ (SmallPresheaf→Presheaf C ℓP P) Cᴰ ℓPᴰ
  SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-obᴰ =
    SmallFunctorᴰ.Functorᴰ.F-obᴰ Pᴰ
  SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-homᴰ =
    SmallFunctorᴰ.Functorᴰ.F-homᴰ Pᴰ
  SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-idᴰ =
    SmallFunctorᴰ.Functorᴰ.F-idᴰ Pᴰ
  SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-seqᴰ =
    SmallFunctorᴰ.Functorᴰ.F-seqᴰ Pᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓP : Level} {P : Presheaf C ℓP}
  {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
  {ℓPᴰ : Level}
  where
  open Functorᴰ
  open FibNatTransᴰDefs (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ
  private
    module SETⱽᴰ = CategoryᴰNotation (SETᴰ.vᴰ[ liftω ℓP ][ liftω ℓPᴰ ])
    module SETⱽᴰ' = SmallCatFiber.Fibers (SmallCatᴰSetsᴰ.SETᴰ ℓP ℓPᴰ)
    module SFunctor = SmallFunctor.Functor
    module SFunctorᴰ = SmallFunctorᴰ.Functorᴰ

  SmallPresheafᴰ→Presheafᴰ : SmallPresheafᴰ P Cᴰ ℓPᴰ → Presheafᴰ P Cᴰ ℓPᴰ
  SmallPresheafᴰ→Presheafᴰ Pᴰ .F-obᴰ =
    λ z → liftω (SmallFunctorᴰ.Functorᴰ.F-obᴰ Pᴰ (z .lowerω))
  SmallPresheafᴰ→Presheafᴰ Pᴰ .F-homᴰ = SmallFunctorᴰ.Functorᴰ.F-homᴰ Pᴰ
  SmallPresheafᴰ→Presheafᴰ Pᴰ .F-idᴰ {x = x} {xᴰ = xᴰ} =
    SETⱽᴰ.≡in {yᴰ = liftω (SmallFunctorᴰ.Functorᴰ.F-obᴰ Pᴰ (xᴰ .lowerω))} $
      SmallFunctorᴰ.Functorᴰ.F-idᴰ Pᴰ
  SmallPresheafᴰ→Presheafᴰ Pᴰ .F-seqᴰ fᴰ gᴰ =
    SETⱽᴰ.≡in {yᴰ = liftω (SmallFunctorᴰ.Functorᴰ.F-obᴰ Pᴰ (_ .lowerω))} $
      SmallFunctorᴰ.Functorᴰ.F-seqᴰ Pᴰ fᴰ gᴰ

  Presheafᴰ→SmallPresheafᴰ : Presheafᴰ P Cᴰ ℓPᴰ → SmallPresheafᴰ P Cᴰ ℓPᴰ
  Presheafᴰ→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-obᴰ = λ z → F-obᴰ Pᴰ (liftω z) .lowerω
  Presheafᴰ→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-homᴰ = F-homᴰ Pᴰ
  Presheafᴰ→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-idᴰ =
    SETⱽᴰ'.rectify $ SETⱽᴰ'.≡out $ F-idᴰ Pᴰ
  Presheafᴰ→SmallPresheafᴰ Pᴰ .SmallFunctorᴰ.Functorᴰ.F-seqᴰ fᴰ gᴰ =
    SETⱽᴰ'.rectify $ SETⱽᴰ'.≡out $ F-seqᴰ Pᴰ fᴰ gᴰ

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓP : Level} (P : SmallPresheaf C ℓP)
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  open Functorᴰ
  private
    Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ
    module SFunctor = SmallFunctor.Functor
    module SFunctorᴰ = SmallFunctorᴰ.Functorᴰ
  SmallPresheafᴰOverSmallPresheaf→Presheafᴰ :
    SmallPresheafᴰOverSmallPresheaf P Cᴰ ℓPᴰ → Presheafᴰ (SmallPresheaf→Presheaf C ℓP P) Cᴰ ℓPᴰ
  SmallPresheafᴰOverSmallPresheaf→Presheafᴰ Pᴰ =
    SmallPresheafᴰ→Presheafᴰ (SmallPresheafᴰOverSmallPresheaf→SmallPresheafᴰ Pᴰ)

open Functor
module PresheafᴰNotation {C : SmallCategory ℓC ℓC'} {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ}
   {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module P = PresheafNotation P

  open SmallPshᴰ.PresheafᴰNotation (Presheafᴰ→SmallPresheafᴰ Pᴰ) public

open Functorᴰ
module _
  {C : SmallCategory ℓC ℓC'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {c : C .SmallCategory.small-ob}
  (cᴰ : Cᴰ .SmallCategoryᴰ.small-obᴰ c)
  where
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    Cᴰ' = SmallLocallySmallCategoryᴰ→SmallCategoryᴰ Cᴰ

  open FibNatTransᴰDefs (Cᴰ ^opsmallᴰ) (weaken LEVEL LEVEL) SET SETᴰ

  _[-][-,_] : Presheafᴰ (C [-, c ]) Cᴰ ℓCᴰ'
  _[-][-,_] = SmallPresheafᴰOverSmallPresheaf→Presheafᴰ _ Cᴰ ℓCᴰ' (Cᴰ' SmallCatᴰSetsᴰ.[-][-, cᴰ ])

  _[-][-,_]' : Presheafᴰ (C [-, c ]) Cᴰ ℓCᴰ'
  _[-][-,_]' .F-obᴰ cᴰ' = liftω λ f → Cᴰ.Hom[ f ][ cᴰ' , liftω cᴰ ] , Cᴰ.isSetHomᴰ
  _[-][-,_]' .F-homᴰ fᴰ = λ _ gᴰ → fᴰ Cᴰ.⋆ᴰ gᴰ
  _[-][-,_]' .F-idᴰ  =
    ΣPathP ((funExt λ _ → C.⋆IdL _) , (funExt₂ λ _ _ → Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _))
  _[-][-,_]' .F-seqᴰ fᴰ gᴰ =
    ΣPathP ((funExt λ _ → C.⋆Assoc _ _ _) , funExt₂ λ _ _ → Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _)

  private
    -- The manual definition and the compositional definition
    -- of the displayed representable are defintionally isomorphic
    -- Although we have to map into the type of small displayed
    -- functors to consider paths
    _ : SmallLocallySmallFunctorᴰ→SmallFunctorᴰ
      {Cᴰ = Cᴰ ^opsmallᴰ}
      {Dᴰ = SETᴰAtEq ℓC' ℓCᴰ'}
      _[-][-,_] ≡
        SmallLocallySmallFunctorᴰ→SmallFunctorᴰ _[-][-,_]'
    _ = SmallFunctorᴰ.Functorᴰ≡ (λ _ → refl) (λ _ → refl)

module _  where
  open SmallCategoryᴰVariables
  open SmallCategoryᴰ

  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    (α : PshHom P Q)
    {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where
    PshHomᴰ : Type _
    PshHomᴰ = PSHᴰ.Hom[ _ , _ , α ][ Pᴰ , Qᴰ ]

  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    (α : PshIso P Q)
    {Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ'}
    (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
    (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
    where
    private
      module LEVEL×PSH = CategoryᴰNotation (LEVEL×PSH Cᴰ)
      the-iso : CatIso LEVEL×PSH.∫C
        (liftω ℓP , (liftω ℓPᴰ , P)) (liftω ℓQ , (liftω ℓQᴰ , Q))
      the-iso .CatIso.fun = tt , (tt , (α .CatIsoᴰ.funᴰ))
      the-iso .CatIso.inv = tt , (tt , (α .CatIsoᴰ.invᴰ))
      the-iso .CatIso.sec i = tt , α .CatIsoᴰ.secᴰ i
      the-iso .CatIso.ret i = tt , α .CatIsoᴰ.retᴰ i
    PshIsoᴰ : Type _
    PshIsoᴰ = PSHISOᴰ.Hom[ the-iso ][ Pᴰ , Qᴰ ]
