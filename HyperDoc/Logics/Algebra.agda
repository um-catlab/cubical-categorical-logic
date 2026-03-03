{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logics.Algebra where 
  
open import Cubical.Data.Sigma 
open import Cubical.Data.Unit
open import Cubical.Data.FinData hiding (rec ; elim ; eq)

open import Cubical.Foundations.Prelude 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Powerset
open import Cubical.Functions.Logic
open import  Cubical.HITs.PropositionalTruncation.Base
open import  Cubical.HITs.PropositionalTruncation.Properties

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Algebra.Algebra hiding (Model)
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Logic.Base
open import HyperDoc.CBPV.Model.Algebra
open import HyperDoc.Logics.SetPred
open import HyperDoc.Logic.Structure
open import HyperDoc.CBPV.TypeStructure
import HyperDoc.CBPV.Syntax.U1 as SyntaxU1
import HyperDoc.CBPV.Syntax.UF1 as SyntaxUF1
open import HyperDoc.Lib

open Alg
open AlgHom
open Category
open Functor
open NatTrans
open PshHom 
open PshIso
open Iso

module AlgLog (Σ : Signature) where
  open Model Σ
  AlgLogic : Logic AlgModel
  AlgLogic .Logic.VH = Pred
  AlgLogic .Logic.CH = AlgPred Σ
  AlgLogic .Logic.Sq .N-ob (A , B) M .MonFun.f (Q , clQ) a = Q (M a)
  AlgLogic .Logic.Sq .N-ob (A , B) M .MonFun.isMon Q a = Q (M a)
  AlgLogic .Logic.Sq .N-hom f = refl
  AlgLogic .Logic.pullOp op args P Q prf a Pa = Q .snd op (λ z → args z a , prf z a Pa)

  module U1 where 
    open SyntaxU1.SyntacticModel Σ using (SynModel)
    open SyntaxU1.Syntax Σ 
    private 
      module Syn = CBPVModel SynModel

    -- Global Section Functor
    CL : CBPVMorphism SynModel AlgModel
    CL .CBPVMorphism.FV = Syn.V [ 𝟙 ,-]
    CL .CBPVMorphism.FC = Syn.O[ 𝟙 ,-]
    CL .CBPVMorphism.FO .N-ob (A , B) .carmap M V = subC V M
    CL .CBPVMorphism.FO .N-ob (A , B) .pres op args = 
      funExt λ V → opsSub V op args
    CL .CBPVMorphism.FO .N-hom (V , S) = 
      AlgHom≡ (
        funExt λ M → 
        funExt λ W → plugSub ∙ cong₂ plug refl (subDist ∙ sym subCId))

  module UF1 where 
    open SyntaxUF1.SyntacticModel Σ using (SynModel)
    open SyntaxUF1.Syntax Σ 
    open Push AlgLogic
    open CBPVModel AlgModel
    open Signature Σ 
    private 
      module Syn = CBPVModel SynModel

    -- Global Section Functor
    CL : CBPVMorphism SynModel AlgModel
    CL .CBPVMorphism.FV = Syn.V [ 𝟙 ,-]
    CL .CBPVMorphism.FC = Syn.O[ 𝟙 ,-]
    CL .CBPVMorphism.FO .N-ob (A , B) .carmap M V = subC V M
    CL .CBPVMorphism.FO .N-ob (A , B) .pres op args = 
      funExt λ V → opsSub V op args
    CL .CBPVMorphism.FO .N-hom (V , S) = 
      AlgHom≡ (
        funExt λ M → 
        funExt λ W → plugSub ∙ cong₂ plug refl (subDist ∙ sym subCId))

    data DirectImageCong' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ B .Carrier ⟩ → Type where 
      base : (b : ⟨ B .Carrier ⟩ )(a : ⟨ A ⟩ ) → M a ≡ b → a ∈ P → DirectImageCong' A B M P b
      step : 
            (op : Op)
            (args : Fin (arity op) → ⟨ B .Carrier ⟩ )
            (dargs : (a : Fin (arity op)) → DirectImageCong' A B M P (args a) ) → 
            DirectImageCong' A B M P (B .interp op args)

    DICong-elim : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → 
      (motive : ∀ (b : ⟨ B. Carrier ⟩) → DirectImageCong' A B M P b  → Type)
      (base-case : 
        (b : ⟨ B .Carrier ⟩) 
        (a : ⟨ A ⟩ ) 
        (eq : M a ≡ b)
        (a∈P : a ∈ P) → 
        motive b (base b a eq a∈P ))
      (step-case : 
        (op : Op)
        (args : Fin (arity op) → ⟨ B .Carrier ⟩)
        (dargs : (a : Fin (arity op)) → DirectImageCong' A B M P (args a)) 
        (motives : (a : Fin (arity op)) → motive (args a) (dargs a) ) → 
        motive (B .interp op args) (step op args dargs)) 

      → (b : ⟨ B .Carrier ⟩) → (C : DirectImageCong' A B M P b) → motive b C  
    DICong-elim A B M P mot bc sc b (base b₁ a eq prf) = 
      bc b a eq prf
    DICong-elim A B M P mot bc sc b (step op args dargs) = 
      sc op args dargs λ a → DICong-elim A B M P mot bc sc (args a) (dargs a)


    DirectImageCong : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → ℙ ⟨ B .Carrier ⟩
    DirectImageCong A B M P b = ∥ DirectImageCong' A B M P b ∥ₚ

    push' : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      ℙ ⟨ A ⟩ → SubAlg B
    push' {A} {B} M P .fst = DirectImageCong A B M P
    push' {A} {B} M P .snd op args = goal where 

      b' : ⟨ B .Carrier ⟩  
      b' = interp B op (λ a → args a .fst)

      goal : b' ∈ (DirectImageCong A B M P)
      goal = 
        recFin 
          {m = arity op} 
          squash₁ 
          (λ x → ∣ (step op (λ a → args a .fst) x) ∣₁) 
          (λ a → args a .snd)


    push : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      MonFun (pred A .fst) (subAlgPo B .fst) 
    push {A} {B} M .MonFun.f = push' {A}{B} M
    push {A} {B} M .MonFun.isMon {P}{Q} P≤Q b = map goal where 
      goal : DirectImageCong' A B M P b → DirectImageCong' A B M Q b
      goal = 
        DICong-elim A B M P 
          (λ b _  → DirectImageCong' A B M Q b) 
          (λ b₁ a eq a∈P → base b₁ a eq (P≤Q a a∈P)) 
          (λ op args dargs → step op args) 
          b

    hasPush : HasPush
    hasPush M .fst = push M
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .fun = goal where 
      goal : 
        ((b : fst (Carrier B)) →
        ∥ DirectImageCong' A B M P b ∥₁ → b ∈ (Q .fst)) →
        (a : fst A) → a ∈ P  → (M a) ∈ (Q .fst)
      goal trans a Pa = trans (M a) ∣ (base (M a) a refl Pa) ∣₁

    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q}  .inv = goal where 
      goal : 
        ((a : fst A) → a ∈ P → (M a) ∈ (Q .fst)) →
        (b : fst (Carrier B)) → ∥ DirectImageCong' A B M P b ∥₁ → b ∈ (Q .fst)
      goal tran b = 
        rec 
          (∈-isProp (λ z → z) (Q .fst b)) 
          (DICong-elim A B M P 
            (λ b _ → b ∈ (Q .fst)) 
            (λ b a eq a∈P → subst (λ h → h ∈ (Q .fst)) eq (tran a a∈P)) 
            (λ op args dargs mot → Q .snd op (λ z → args z , mot z)) 
            b)
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .sec b = ⊆-isProp P (λ x → Q .fst  (M x)) _ b
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .Iso.ret a = ⊆-isProp (DirectImageCong A B M P) (Q .fst) _ a
