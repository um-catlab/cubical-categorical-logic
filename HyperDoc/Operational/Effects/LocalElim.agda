{-# OPTIONS --type-in-type #-}
{-# OPTIONS --lossy-unification #-}

module HyperDoc.Operational.Effects.LocalElim where 

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)
open import Cubical.Categories.Displayed.Section.Base

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.Model
open import HyperDoc.Operational.Effects.Logic
open import HyperDoc.Operational.Effects.Elim
open import HyperDoc.Operational.Effects.Section
open import HyperDoc.Operational.Effects.Syntax
open import HyperDoc.Operational.Effects.TypeStructure

open NatTransᴰ

module LocalElimLogic 
  {Sig : Signature}
  {N : CBPVModel Sig }
  (L : CBPVLogic N)
  (LHas𝟙ᴸ : LogicStruct.Has𝟙ᴸ L)
  (LHas+ᴸ : LogicStruct.Has+ᴸ L)
  (LHasFTyᴸ : LogicStruct.HasFTyᴸ L) where 

  open Elim
  open HyperDoc.Operational.Effects.Syntax
  open SynModel Sig 

  open TypeStructureᴰ
  open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)
  open import HyperDoc.Syntax
  -- open ConvertLogic L

  module _ (F : CBPVMorphism Syn N) where

    open Reindex F L 
    L' : CBPVLogic Syn 
    L' = reindex 

    module LMHV = HDSyntax (CBPVLogic.LV L')
    module LMHC = HDSyntax (CBPVLogic.LC L')
    open LogicalToDisplayed L'

    Synᴰ : CBPVModelᴰ Syn 
    Synᴰ = ConvertLogic.Mᴰ L'

    -- this is just UTyDep.hasUTyᴰ hasUTy, 
    dumb : HasUTyᴰ Synᴰ hasUTy
    dumb Bᴰ .WkRepresentationᴰ.repᴰ = UTyDep.hasUTyᴰ hasUTy  Bᴰ .WkRepresentationᴰ.repᴰ
    dumb Bᴰ .WkRepresentationᴰ.fwdᴰ .N-obᴰ xᴰ x x₁ = UTyDep.hasUTyᴰ hasUTy  Bᴰ .WkRepresentationᴰ.fwdᴰ .N-obᴰ xᴰ x x₁
    dumb Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ fᴰ i x y = UTyDep.hasUTyᴰ hasUTy  Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ fᴰ i x y
    dumb Bᴰ .WkRepresentationᴰ.bkwdᴰ = UTyDep.hasUTyᴰ hasUTy  Bᴰ .WkRepresentationᴰ.bkwdᴰ
    dumb Bᴰ .WkRepresentationᴰ.wkretractᴰ = UTyDep.hasUTyᴰ hasUTy  Bᴰ .WkRepresentationᴰ.wkretractᴰ

    -- Now trying to fill the hole with ( Elim ? ? ? ? ?) takes forever..
    --GlobalElim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
   -- GlobalElim = {! Elim ? ? ? ? ?   !}

    GlobalElim : CBPVSection {F = idModelMorphsim Syn}{Synᴰ} 
    GlobalElim = 
      Elim 
        Synᴰ 
        (𝟙TyDep.has𝟙ᴰ has𝟙 (pres𝟙ᴸ LHas𝟙ᴸ)) 
        (+TyDep.has+ᴰ has+ (pres+ᴸ LHas+ᴸ)) 
        dumb --  (UTyDep.hasUTyᴰ hasUTy) -- jfc, good luck waiting for the type checker to finish
        (FTyDep.hasFTyᴰ hasFTy (presFTyᴸ LHasFTyᴸ)) 
      

    LocalElim : CBPVSection {F = F}{ConvertLogic.Mᴰ L}
    LocalElim .fst = 
      GlobalSectionReindex→Section 
        (CBPVModelᴰSyntax.Vᴰ (ConvertLogic.Mᴰ L)) 
        (CBPVMorphismSyntax.FV F) 
        conv where 

        conv : GlobalSection
          (reindexᴰ (CBPVModelᴰSyntax.Vᴰ (ConvertLogic.Mᴰ L))
          (CBPVMorphismSyntax.FV F))
        conv  .Section.F-obᴰ = GlobalElim .fst .Section.F-obᴰ
        conv  .Section.F-homᴰ = GlobalElim .fst .Section.F-homᴰ
        conv  .Section.F-idᴰ = toPathP (LMHV.isProp≤  _ _)
        conv  .Section.F-seqᴰ _ _ = toPathP (LMHV.isProp≤  _ _)

    LocalElim .snd .fst = 
      GlobalSectionReindex→Section 
        (CBPVModelᴰSyntax.Cᴰ (ConvertLogic.Mᴰ L)) 
        (CBPVMorphismSyntax.FC F) 
        conv where 

        conv : GlobalSection
          (reindexᴰ (CBPVModelᴰSyntax.Cᴰ (ConvertLogic.Mᴰ L))
          (CBPVMorphismSyntax.FC F))
        conv  .Section.F-obᴰ = GlobalElim .snd .fst .Section.F-obᴰ
        conv  .Section.F-homᴰ = GlobalElim .snd .fst .Section.F-homᴰ
        conv  .Section.F-idᴰ = toPathP (LMHC.isProp≤ _ _)
        conv  .Section.F-seqᴰ _ _ = toPathP (LMHC.isProp≤ _ _)
    LocalElim .snd .snd .SectionNat.F-Car {A}{B} M = GlobalElim .snd .snd .SectionNat.F-Car M
    LocalElim .snd .snd .SectionNat.F-Edge n↦n' = tt
    --LocalElim .snd .snd .SectionNat.F-Node-nat V S M = toPathP ((LMHV.isProp≤ _ _))
   -- LocalElim .snd .snd .SectionNat.F-Edge-nat V S M M' e = toPathP (isPropUnit _ _) 
