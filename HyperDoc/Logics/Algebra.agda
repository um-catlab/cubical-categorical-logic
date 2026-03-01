{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logics.Algebra where 
  
open import Cubical.Data.Sigma 
open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Logic.Base
open import HyperDoc.CBPV.Model.Algebra
open import HyperDoc.Logics.SetPred
open import HyperDoc.CBPV.TypeStructure
open import HyperDoc.CBPV.Syntax.U1

open Alg
open AlgHom
open Category
open Functor
open NatTrans
open PshHom 
open PshIso

module AlgLog (Σ : Signature) where
  AlgLogic : Logic (AlgModel Σ)
  AlgLogic .Logic.VH = Pred
  AlgLogic .Logic.CH = AlgPred Σ
  AlgLogic .Logic.Sq .N-ob (A , B) M .MonFun.f (Q , clQ) a = Q (M a)
  AlgLogic .Logic.Sq .N-ob (A , B) M .MonFun.isMon Q a = Q (M a)
  AlgLogic .Logic.Sq .N-hom f = refl
  AlgLogic .Logic.pullOp op args P Q prf a Pa = Q .snd op (λ z → args z a , prf z a Pa)

  unit : TypeStructure.HasV𝟙 (AlgModel Σ)
  unit .fst = Unit , isSetUnit
  unit .snd .trans .N-ob c x = tt
  unit .snd .trans .N-hom _ _ _ _  = refl
  unit .snd .nIso x .fst = λ _ _ → tt
  unit .snd .nIso x .snd .fst tt = refl
  unit .snd .nIso x .snd .snd a  = funExt λ x₁ i → tt

  open SyntacticModel Σ
  open Syntax Σ
  private 
    module Syn = CBPVModel SynModel

  -- Global Section Functor
  CL : CBPVMorphism SynModel (AlgModel Σ)
  CL .CBPVMorphism.FV = V [ 𝟙 ,-]
  CL .CBPVMorphism.FC = Syn.O[ 𝟙 ,-]
  CL .CBPVMorphism.FO .N-ob (A , B) .carmap M V = subC V M
  CL .CBPVMorphism.FO .N-ob (A , B) .pres op args = 
    funExt λ V → opsSub V op args
  CL .CBPVMorphism.FO .N-hom (V , S) = 
    AlgHom≡ (
      funExt λ M → 
      funExt λ W → plugSub ∙ cong₂ plug refl (subDist ∙ sym subCId))