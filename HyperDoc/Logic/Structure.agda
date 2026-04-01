{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logic.Structure where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Logic.Base
open import HyperDoc.Syntax

open Category
open Functor

module Push
  {Σ : Signature} 
  {M : CBPVModel Σ}
  (L : Logic M) where 

  open CBPVModel M 
  open Logic L

  private 
    module VL = HDSyntax VH 
    module CL = HDSyntax CH 

  HasPush : Type
  HasPush = 
    ∀ {A : V .ob}
      {B : C .ob} → 
      (M : O'[ A , B ]) → 
      HasLeftAdj (pull M)

  module PushSyntax (pp : HasPush) where 
    open import Cubical.Foundations.Isomorphism
    open Iso
    open _⊣_ 
    pushToPull : 
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q  → 
      A VL.◂ P ≤ pull M .MonFun.f Q
    pushToPull M  = adjIff (pp M .snd) .fun 

    pullToPush : 
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      A VL.◂ P ≤ pull M .MonFun.f Q → 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q 
    pullToPush M  = adjIff (pp M .snd) .inv 

    pullPush :       
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {Q : CL.F∣ B ∣}
      → A VL.◂ pull M .MonFun.f Q ≤ pull M .MonFun.f Q
    pullPush M = pushToPull M (pullToPush M VL.id⊢)
      
-- ∃
module VPush   
  {Σ : Signature} 
  {M : CBPVModel Σ}
  (L : Logic M) where 

  open CBPVModel M 
  open Logic L

  private 
    module VL = HDSyntax VH 

  HasVPush : Type
  HasVPush = 
    ∀ {A A' : V .ob}
      (f : V [ A , A' ]) → 
      HasLeftAdj (VH .F-hom f)

-- ∃
module CPush   
  {Σ : Signature} 
  {M : CBPVModel Σ}
  (L : Logic M) where 

  open CBPVModel M 
  open Logic L

  private 
    module CL = HDSyntax CH 

  HasCPush : Type
  HasCPush = 
    ∀ {B B' : C .ob}
      (f : C [ B , B' ]) → 
      HasLeftAdj (CH .F-hom f)