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
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.HITs.PropositionalTruncation.Properties

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
import HyperDoc.CBPV.Syntax.UF1+derived as SyntaxUF1+
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

  module _  (Σ : Signature) where 
    open import HyperDoc.Connectives.Connectives

    Ahas⊤ : L⊤.Has⊤ (AlgPred Σ)
    Ahas⊤ .fst A .L⊤.HA.top .fst x = ⊤
    Ahas⊤ .fst A .L⊤.HA.top .snd op args = tt*
    Ahas⊤ .fst A .L⊤.HA.top-top = λ x _ → tt*
    Ahas⊤ .snd f .L⊤.HAHom.f-top = SubAlg≡ _ _ ((λ x _ → tt*) , (λ x _ → tt*))

    Ahas∧ : L∧.Has∧  (AlgPred Σ)
    (Ahas∧ .fst c L∧.HA.∧ P) Q .fst = P .fst ∩ Q .fst
    (Ahas∧ .fst c L∧.HA.∧ P) Q .snd op args = P .snd op (λ z → args z .fst , args z .snd .fst) ,
      Q .snd op (λ z → args z .fst , args z .snd .snd)
    Ahas∧ .fst c .L∧.HA.and-intro = λ z z₁ x z₂ → z x z₂ , z₁ x z₂
    Ahas∧ .fst c .L∧.HA.and-elim1 = λ z x z₁ → z x z₁ .fst
    Ahas∧ .fst c .L∧.HA.and-elim2 = λ z x z₁ → z x z₁ .snd
    Ahas∧ .snd f .L∧.HAHom.f-and P Q  = SubAlg≡ _ _ ((λ x z → z) , (λ x z → z))

    
    open Signature
    data _⨁p'_ {A : Alg Σ}(P Q : SubAlg A) : ⟨ A .Carrier ⟩ → Type where 
      in₁ : ∀ (a : ⟨ A .Carrier ⟩) → a ∈ P .fst → _⨁p'_ P Q a
      in₂ : ∀ (a : ⟨ A .Carrier ⟩) → a ∈ Q .fst → _⨁p'_ P Q a
      ⊕op : (op : Op Σ)(args : Fin (arity Σ op) →  Σ[ a ∈ ⟨ A .Carrier ⟩ ]  ∥ _⨁p'_ {A} P Q a ∥₁) → 
        _⨁p'_ P Q (A .interp op λ a → args a .fst)


    _⨁p_ : {A : Alg Σ}(P Q : SubAlg A) → SubAlg A 
    _⨁p_ {A} P Q .fst a = ∥ _⨁p'_ {A} P Q a ∥ₚ
    _⨁p_ {A} P Q .snd op args = recFin squash₁ (λ z → ∣ ⊕op op (λ z₁ → args z₁ .fst , args z₁ .snd) ∣₁) λ a → args a .snd
      -- ∣ ⊕op op (λ a → {!  args a !}) ∣₁

    -- This should be safe
    {-# TERMINATING #-}
    ⨁pelim : {A : Alg Σ}{P Q R : SubAlg A} → 
      (∀ (a : ⟨ A .Carrier ⟩) → a ∈ Q .fst → a ∈ P .fst) → 
      (∀ (a : ⟨ A .Carrier ⟩) → a ∈ R .fst → a ∈ P .fst) → 
      (∀ (a : ⟨ A .Carrier ⟩) →  ∥ (_⨁p'_{A} Q R) a ∥₁ → a ∈ P .fst) 
    ⨁pelim {A}{P}{Q}{R} f g a x = rec (∈-isProp (λ z → z) (P .fst a)) (goal a) x where 

      goal : ∀ (a : ⟨ A .Carrier ⟩) → (_⨁p'_ {A} Q R) a → a ∈ P .fst
      goal _ (in₁ a x) = f a x
      goal _ (in₂ a x) = g a x
      goal _ (⊕op op args) = P .snd op args' where

        args' : Fin (arity Σ op) → Σ[ a ∈ ⟨ Carrier A ⟩ ] (a ∈ P .fst)
        args' x .fst = args x .fst
        args' x .snd = rec (∈-isProp (λ z → z) (P .fst (args x .fst))) (goal (args x .fst)) (args x .snd)
    
    -- same issue, 
    {-# TERMINATING #-}
    Ahas∨ : L∨.Has∨ (AlgPred Σ)
    Ahas∨ .fst A .L∨.HA._∨_ P Q = _⨁p_ {A} P Q
    Ahas∨ .fst A .L∨.HA.or-intro1 f a Pa = ∣ (in₁ a (f a Pa)) ∣₁
    Ahas∨ .fst A .L∨.HA.or-intro2 f a Pa = ∣ (in₂ a (f a Pa)) ∣₁
    Ahas∨ .fst A .L∨.HA.or-elim = ⨁pelim {A}
    Ahas∨ .snd {A}{A'} h .L∨.HAHom.f-or P Q = 
        SubAlg≡ {Σ}{A'} _ _ 
          ((λ a'  → map (goal1 a')) , 
          λ a' → map (goal2 a') ) where 

            -- cant match on indexed inductive where index is of form (f b) 
            goal1 : ∀(a' : ⟨ A' .Carrier ⟩) →  (P ⨁p' Q) (h .carmap a') → (AlgPred Σ .F-hom h .MonFun.f P ⨁p' AlgPred Σ .F-hom h .MonFun.f Q) a' 
            goal1 a' x = {!  x !}

            goal2 : ∀(a' : ⟨ A' .Carrier ⟩) →  (AlgPred Σ .F-hom h .MonFun.f P ⨁p' AlgPred Σ .F-hom h .MonFun.f Q) a' → (P ⨁p' Q) (h .carmap a') 
            goal2 a' (in₁ a x) = in₁ (h .carmap a') x
            goal2 a' (in₂ a x) = in₂ (h .carmap a') x
            goal2 a' (⊕op op args) = subst  
              ((_⨁p'_ {A} P Q))  (sym (h .pres op λ a → args a .fst)) (⊕op op λ x → (h .carmap (args x .fst)) , rec squash₁ (λ p → ∣ (goal2 (args x .fst) p) ∣₁) (args x .snd))

    open CPush (AlgLogic)
    open VPush (AlgLogic)
    open import Cubical.Relation.Binary.Preorder
    open IsPreorder
    open PreorderStr
    open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint


    ∃f' : {A A' : hSet _ } → (f : ⟨ A ⟩ → ⟨ A' ⟩ ) → ℙ ⟨ A ⟩ → ℙ ⟨ A' ⟩ 
    ∃f' {A}{A'} f P a' = ∥ (Σ[ a ∈ ⟨ A ⟩  ]  (f a ≡ a') × ⟨ P a ⟩) ∥ₚ

    hasVPush : HasVPush
    hasVPush {A}{A'} f .fst .MonFun.f = ∃f' {A}{A'} f
    hasVPush {A}{A'} f .fst .MonFun.isMon x≤y a' = map λ z → z .fst , z .snd .fst , x≤y (z .fst) (z .snd .snd)
    hasVPush f .snd ._⊣_.adjIff {P}{Q} .fun prf a Pa = prf (f a) ∣ (a , (refl , Pa)) ∣₁
    hasVPush f .snd ._⊣_.adjIff {P}{Q} .inv prf a' = rec (Q a' .snd) λ {(a , eqn , Pa) → subst (λ h → h ∈ Q) eqn (prf a  Pa)}
    hasVPush {A}{A'} f .snd ._⊣_.adjIff {P}{Q} .sec b = pred  A .fst .snd .is-prop-valued P (Pred .F-hom {A'}{A} f $ Q)  _ _ 
    hasVPush {A}{A'} f .snd ._⊣_.adjIff {P}{Q} .ret a = pred  A' .fst .snd .is-prop-valued (λ x → _ , squash₁) Q   _ _


    ∃f : {Σ : Signature} {B B' : Alg Σ} → (f : ALG Σ [ B , B' ] ) → SubAlg B → SubAlg B' 
    ∃f {Σ}{B}{B'} f P .fst = ∃f' {B .Carrier}{B' .Carrier} (f .carmap) (P .fst)
    ∃f {Σ}{B}{B'} f P .snd op args = goal where 


      goal : interp B' op (λ i → args i .fst) ∈  ∃f' {B .Carrier}{B' .Carrier} (f .carmap) (P .fst)
      goal = recFin squash₁ 
        (λ x → 
          ∣ ((B .interp op (λ z → x z .snd .fst)) ,   -- x z .fst ≡ args z .fst ,   this is true 
            f .pres op (λ z → x z .snd .fst) ∙ cong (λ h → interp B' op h) (funExt (λ z → x z .snd .snd .fst ∙ {!   !})) , 
            P .snd op λ z → x z .snd .fst , x z .snd .snd .snd) ∣₁) 
        (λ x → existsΣ (args x))

    hasCPush : HasCPush
    hasCPush {B}{B'} f .fst .MonFun.f = ∃f {_}{B}{B'} f
    hasCPush f .fst .MonFun.isMon x≤y b' = map λ z → z .fst , z .snd .fst , x≤y (z .fst) (z .snd .snd)
    hasCPush {B} {B'} f .snd ._⊣_.adjIff {P} {Q} .fun prf b Pb = prf (f .carmap b) ∣ (b , (refl , Pb)) ∣₁
    hasCPush {B} {B'} f .snd ._⊣_.adjIff {P} {Q} .inv prf a' = rec (∈-isProp (λ z → z) (Q .fst a') ) λ {(b , eqn , Pb) → subst (λ h → h ∈ Q .fst) eqn  (prf b Pb)}
    hasCPush {B} {B'} f .snd ._⊣_.adjIff {P} {Q} .sec b = subAlgPo B .fst .snd .is-prop-valued P {!   !} _ _
    hasCPush {B} {B'} f .snd ._⊣_.adjIff {P} {Q} .ret a = subAlgPo B' .fst .snd .is-prop-valued (∃f f P) Q  _ _

  module U1 where 
    open SyntaxU1.SyntacticModel Σ using (SynModel)
    open SyntaxU1.Syntax Σ 
    private 
      module Syn = CBPVModel SynModel

    -- TOOD why is this here? move
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
     --  isPropDI : (b : ⟨ B .Carrier ⟩) → isProp (DirectImageCong' A B M P b)

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

  module UF1+ where 
    open SyntaxUF1+.SyntacticModel Σ using (SynModel)
    open SyntaxUF1+.Syntax Σ 
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
