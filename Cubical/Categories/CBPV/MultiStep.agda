{-# OPTIONS --lossy-unification #-}

module Cubical.Categories.CBPV.MultiStep where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.CoData.Delay

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.CBPV.Functor
open import Cubical.Categories.CBPV.Instances.TransitionSystem
open import Cubical.Categories.CBPV.Instances.Kleisli
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.FromCat 
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TransitionSystem
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets
  renaming (SET to SETSCwF)

open CBPVFunctor
open CBPVModel
open EnrichedFunctor
open Functor
open PshHom
open TSystem
open TSystem[_,_]

private 
  variable
    ℓ : Level 

module _ (ℓ : Level) where 

  IdPreFun : PreFunctor (SETSCwF ℓ) (SETSCwF ℓ)
  IdPreFun .fst = Id
  IdPreFun .snd .fst ty = ty
  IdPreFun .snd .snd .N-ob c x = x
  IdPreFun .snd .snd .N-hom _ _ _ _ = refl

  𝓥 = PshMon.𝓟Mon (SET ℓ) ℓ

  -- F-stacks can be defined by a non enriched functor 
  -- implement enrichF

  S : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  S = (TSystemModel ℓ)

  T : CBPVModel (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ (ℓ-suc ℓ) ℓ 
  T = (Kleisli DExt) 

  _ = {! T .Stacks  !}



  runE : {B B' : TSystem ℓ} → 
    TSysCat [ B , B' ] → (K DExt) [ B .term , B' .term ] 
  runE f t = {!   !}

  EF' : Functor TSysCat (K DExt)
  EF' .F-ob S = S .term
  EF' .F-hom = runE
  EF' .F-id = {!   !}
  EF' .F-seq = {!   !}

  EF : EnrichedFunctor 𝓥 (S . Stacks) (T .Stacks)
  EF = Functor→Enriched TSysCat (K DExt) EF' 



  MultiStep : CBPVFunctor S T
  MultiStep .PreF = IdPreFun
  MultiStep .F-stacks = {!   !}
  MultiStep .F-comp = {!   !}
