{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.Logics.Algebra where 
  
open import Cubical.Data.Sigma 
open import Cubical.Data.Unit
open import Cubical.Data.FinData hiding (rec ; elim)

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

open import HyperDoc.Algebra.Algebra
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

  module U1 where 
    open SyntaxU1.SyntacticModel Σ using (SynModel)
    open SyntaxU1.Syntax Σ 
    private 
      module Syn = CBPVModel SynModel

    -- Global Section Functor
    CL : CBPVMorphism SynModel (AlgModel Σ)
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
    private 
      module Syn = CBPVModel SynModel

    -- Global Section Functor
    CL : CBPVMorphism SynModel (AlgModel Σ)
    CL .CBPVMorphism.FV = Syn.V [ 𝟙 ,-]
    CL .CBPVMorphism.FC = Syn.O[ 𝟙 ,-]
    CL .CBPVMorphism.FO .N-ob (A , B) .carmap M V = subC V M
    CL .CBPVMorphism.FO .N-ob (A , B) .pres op args = 
      funExt λ V → opsSub V op args
    CL .CBPVMorphism.FO .N-hom (V , S) = 
      AlgHom≡ (
        funExt λ M → 
        funExt λ W → plugSub ∙ cong₂ plug refl (subDist ∙ sym subCId))
    open Push AlgLogic
    open CBPVModel (AlgModel Σ)

  {-
    direct : ∀ {A B}(M : O'[ A , B ]) →  ℙ ⟨ A ⟩ →  ℙ ⟨ B .Carrier ⟩ 
    direct {A}{B} M P b = ∥ (Σ[ a ∈ ⟨ A ⟩ ] (a ∈ P) × (b ≡ M a)) ∥ₚ

    open Signature Σ 
    Env : {B : C .ob} → hSet ℓ-zero  
    Env {B} = (Σ[ op ∈ Op ] (Fin (arity op) → ⟨ B .Carrier ⟩)) , {!  ∩sSet !}

    GenTy :  ∀ {A B}(M : O'[ A , B ]) →  ℙ ⟨ A ⟩ →  ℙ ⟨ B .Carrier ⟩ 
    GenTy  {A} {B} M P b = ∥ Gen {A = (Env {B})}{B .Carrier} (λ e b → B .interp (e .fst) (e .snd)) (direct {A}{B} M P) b  ∥ₚ

    GenCong : ∀ {A B}(M : O'[ A , B ]) →  (P : ℙ ⟨ A ⟩) →  Cong {Σ}{B} (λ b → GenTy {A}{B} M P b)
    GenCong {A}{B} M P op args = goal where 
      subgoal : Gen (λ e b → B .interp (e .fst) (e .snd)) (direct M P) (B .interp op (λ z → args z .fst))
      goal : interp B op (λ i → args i .fst) ∈ GenTy {A}{B} M P
      goal = ∣ (step (op , (λ i → args i .fst)) (B .interp op (λ z → args z .fst)) {!   !}) ∣₁
  -}

    -- data Congruence (A : ob V)(B : ob C)(P  ℙ ⟨ A ⟩)  : Type where 

    {-
    Cong : {Σ : Signature}{A : Alg Σ} → ℙ ⟨ Carrier A ⟩  → Type 
  Cong {Σ}{A} P = (op : Op Σ)(args : Fin (arity Σ op) → Σ[ a ∈ ⟨ Carrier A ⟩ ] a ∈ P ) → 
    interp A op (λ i → args i .fst) ∈ P
      -}
    open Signature Σ 

    -- Direct image
    -- the eliminator for this is going to suck
    data Congruence' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ B .Carrier ⟩ → Type where 
      base : (b : ⟨ B .Carrier ⟩ )(a : ⟨ A ⟩ ) → M a ≡ b → a ∈ P → Congruence' A B M P b
      step : (b : ⟨ B .Carrier ⟩ )
            (op : Op)
            (args : Fin (arity op) → ⟨ B .Carrier ⟩ )
            (dargs : (a : Fin (arity op)) → Congruence' A B M P (args a) ) → 
            Congruence' A B M P (B .interp op args)

    Congruence : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → ℙ ⟨ B .Carrier ⟩
    Congruence A B M P b = ∥ Congruence' A B M P b ∥ₚ

    push' : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      ℙ ⟨ A ⟩ → SubAlg B
    push' {A} {B} M P .fst = Congruence A B M P
    push' {A} {B} M P .snd op args = goal where 

      b' : ⟨ B .Carrier ⟩  
      b' = interp B op (λ a → args a .fst)

      goal : b' ∈ (λ b → ∥ Congruence' A B M P b ∥ₚ)
      goal = 
        recFin 
          {m = arity op} 
          squash₁ 
          (λ x → 
            ∣ (step (B .interp op (λ z → args z .fst)) op (λ a → args a .fst) x) ∣₁) 
          (λ a → args a .snd)


    open import Cubical.Functions.Logic
    push : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      MonFun (pred A .fst) (subAlgPo B .fst) 
    push {A} {B} M .MonFun.f = push' {A}{B} M
    push {A} {B} M .MonFun.isMon {P}{Q} P≤Q = goal where 
      goal : (b : ⟨ Carrier B ⟩ ) →  b ∈ Congruence A B M P  → b ∈ Congruence A B M Q
      goal = {!   !}

    hasPush : HasPush
    hasPush M .fst = push M
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .fun = goal where 
      goal : 
        ((b : fst (Carrier B)) →
        ∥ Congruence' A B M P b ∥₁ → b ∈ (Q .fst)) →
        (a : fst A) → a ∈ P  → (M a) ∈ (Q .fst)
      goal trans a Pa = trans (M a) ∣ (base (M a) a refl Pa) ∣₁

    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q}  .inv = goal where 
      goal : 
        ((a : fst A) → a ∈ P → (M a) ∈ (Q .fst)) →
        (b : fst (Carrier B)) → ∥ Congruence' A B M P b ∥₁ → b ∈ (Q .fst)
      goal tran b c = {!   !}
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .sec b = ⊆-isProp P (λ x → Q .fst  (M x)) _ b
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .Iso.ret a = ⊆-isProp (Congruence A B M P) (Q .fst) _ a


    {-
    -- direct image 
    direct : ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
    direct {A} {B} o P b = ∥ (Σ[ a ∈ ⟨ A ⟩ ] (a ∈ P ) × (b ≡ o a) ) ∥ₚ

    push :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ⟨ B .fst ⟩ → Type ℓS
    push {A}{B} o P b = Gen{ℓS = ℓS} {A = M}{(B .fst .fst) , (B .snd)} (B .fst .snd) (direct {A}{B} o P) b 

    pushₚ :  ∀{A : ob 𝓥}{B : ob 𝓒} → (o : (SET ℓS) [ A , U .F-ob B ]) → ℙ ⟨ A ⟩ → ℙ ⟨ B .fst  ⟩ 
    pushₚ {A}{B} o P b = ∥ push {A} {B} o P b  ∥ₚ

    
    {-}
    CBPVLogic .pushV {A} {B} o .f P .fst = pushₚ {A = A }{B}o P
    CBPVLogic .pushV {A} {B} o .f P .snd w b = tmap (step w b)
    CBPVLogic .pushV {A} {B} o .isMon {P}{Q} P⊆Q b = 
      tmap (λ g → 
        Gen-elim 
          (λ b _ → push {A = A} o Q b)  
          (λ b' b'∈direct → base b' (tmap (λ (a , a∈P , b'≡ ) → a  , P⊆Q a a∈P , b'≡) b'∈direct)) 
          (λ a b' g g' → step a b' g') 
          b 
          g)
    CBPVLogic .pullC {A} {B} o .f P a = P .fst (o a)
    CBPVLogic .pullC {A} {B} o .isMon P a = P (o a)
    CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .fun pushP a a∈P = pushP (o a) ∣ (base (o a) ∣ a , a∈P , refl ∣₁) ∣₁
    CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .inv P⊆Q b = trec (∈-isProp (λ z → Q .fst b) b) λ p → 
      Gen-elim 
        (λ b₁ _ → b₁ ∈ Q .fst) 
        ((λ b → 
          trec 
            (Q .fst b .snd) 
            (λ (a , a∈P , b≡) → subst (λ h → h ∈ Q .fst) (sym b≡) (P⊆Q a a∈P)))) 
        (λ a b g → Q .snd a b) 
        b 
        p
    CBPVLogic .pushPullAdj {o = o} .adjIff {P} {Q} .sec b = ⊆-isProp P (λ a → Q .fst (o a))  _ b 
    CBPVLogic .pushPullAdj {A}{_}{o} .adjIff {P} {Q} .ret' a = ⊆-isProp (pushₚ {A = A} o P) (Q .fst) _ a
  -}

    -}