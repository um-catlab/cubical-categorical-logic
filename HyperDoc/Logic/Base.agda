{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.Logic.Base where

open import Cubical.Data.FinData
open import Cubical.Data.Sum

open import Cubical.Foundations.Prelude hiding(_▷_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Bifunctor 
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Functor 
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Lib
open import HyperDoc.Syntax

open Alg
open Algᴰ
open AlgHom
open AlgHomᴰ
open Category
open Categoryᴰ
open Functor
open Functorᴰ
open NatTrans
open Signature

Hom^op :  Functor ((POSET _ _) ×C (POSET _ _)^op) (SET _)
Hom^op .F-ob (P , Q) = (POSET _ _) [ Q , P ] , (POSET _ _) .isSetHom
Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
Hom^op .F-id = funExt λ _ → eqMon _ _ refl
Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl

record Logic {Σ : Signature} (M : CBPVModel Σ) : Type _ where 
  open CBPVModel M
  field 
    VH : Functor (V ^op) (POSET _ _)
    CH : Functor (C ^op) (POSET _ _)
    Sq : NatTrans (FORGET ∘F O) (Hom^op ∘F (VH ×F ((CH ^opF) ∘F to^op^op)))

  private 
    module VL = HDSyntax VH
    module CL = HDSyntax CH
      
  pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
    → MonFun (F-ob CH B .fst) (F-ob VH A .fst)
  pull {A} {B} M = Sq .N-ob (A , B) M
  
  field 
    pullOp : 
      {A : V .ob}{B : C .ob}
      (op : Op Σ)
      (args : (Fin (arity Σ op) → O'[ A , B ]))
      (P : VL.F∣ A ∣)(Q : CL.F∣ B ∣)
      (dargs : (x : Fin (arity Σ op)) → A VL.◂ P ≤ (pull (args x) $ Q))→ 
      A VL.◂ P ≤ (pull (O[ A , B ] .interp op args) $ Q)


  pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (lrcomp V S .carmap M) ≡ MonComp (CH .F-hom S) (MonComp (pull M) (VH .F-hom V))
  pullComp V S M = funExt⁻ (Sq .N-hom (V , S)) M

  pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
    pull (lcomp V .carmap M) ≡ MonComp (pull M) (VH .F-hom V)
  pullLComp V M = pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (VH .F-hom V))) (CH .F-id)

  pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (rcomp S .carmap M) ≡ MonComp (CH .F-hom S) (pull M)
  pullRComp S M = pullComp (V .id) S M ∙ cong₂ MonComp refl (VH .F-id)

  V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : CL.F∣ B ∣}  → A VL.◂ VL.f* V (pull M $ Q) ≤ (pull (lcomp V .carmap M) $ Q) 
  V*M*→VM* = VL.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

  VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : CL.F∣ B ∣} →  A VL.◂ (pull (lcomp V .carmap M) $ Q) ≤ VL.f* V (pull M $ Q)
  VM*→V*M* = VL.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

module Reindex
  {Σ : Signature} 
  {M N : CBPVModel Σ}
  (F : CBPVMorphism M N)
  (L : Logic N) where 

  private 
    module M = CBPVModel M
    module N = CBPVModel N
    module L = Logic L


  open CBPVMorphism F

  VH' : Functor (M.V ^op) (POSET ℓ-zero ℓ-zero) 
  VH' = L.VH ∘F (FV ^opF)

  CH' : Functor (M.C ^op) (POSET ℓ-zero ℓ-zero) 
  CH' = L.CH ∘F (FC ^opF)

  Sq' : NatTrans 
    (FORGET ∘F M.O)  
    (Hom^op ∘F (VH' ×F ((CH' ^opF) ∘F to^op^op)))
  Sq' = 
    seqTrans (FORGET ∘ʳ FO) (
    seqTrans F-assocl (
    seqTrans (L.Sq ∘ˡ ((FV ^opF) ×F FC)) 
    dumb ))  where 

    dumb : NatTrans
      ((Hom^op ∘F (L.VH ×F ((L.CH ^opF) ∘F to^op^op))) ∘F ((FV ^opF) ×F FC))
      (Hom^op ∘F ((L.VH ∘F (FV ^opF)) ×F (((L.CH ∘F (FC ^opF)) ^opF) ∘F to^op^op)))
    dumb .N-ob x z = z
    dumb .N-hom f = refl

  reindex : Logic M 
  reindex .Logic.VH = VH'
  reindex .Logic.CH = CH'
  reindex .Logic.Sq = Sq'
  reindex .Logic.pullOp {A}{B} op args P Q dargs = goal where 
    module VH' = HDSyntax VH'
    module VH = HDSyntax L.VH
      
    pull : {A : M.V .ob}{B : M.C .ob}(M' : M.O'[ A , B ])  
      → MonFun (CH' .F-ob  B .fst) (VH' .F-ob A .fst) 
    pull {A} {B} M = Sq' .N-ob (A , B) M

    opN : N.O'[ F-ob (FV ^opF) A , F-ob (FC ^opF) B ] 
    opN = N.O .F-ob ((F-ob (FV ^opF) A) , (F-ob (FC ^opF) B)) .interp op (λ z → N-ob FO (A , B) .carmap (args z))

    opM : N.O'[ F-ob (FV ^opF) A , F-ob (FC ^opF) B ]
    opM = N-ob FO (A , B) .carmap (M.O .F-ob (A , B) .interp op args)

    have : F-ob (FV ^opF) A VH.◂ P ≤ (L.pull opN  $ Q)
    have = L.pullOp op (λ z → N-ob FO (A , B) .carmap (args z)) P Q dargs

    subgoal' : opN ≡ opM
    subgoal' = sym (N-ob FO (A , B) .pres  op args )

    subgoal : L.pull opN ≡ pull (M.O[ A , B ] .interp op args)
    subgoal = cong L.pull subgoal'

    goal : A VH'.◂ P ≤ (pull (M.O[ A , B ] .interp op args) $ Q)
    goal = VH'.seq have (VH'.eqTo≤ ((cong (λ h → MonFun.f h Q ) subgoal)))


module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open HDSyntax F  

  Cᴰ : Categoryᴰ C _ _ 
  ob[ Cᴰ ] = F∣_∣
  Cᴰ .Hom[_][_,_] {x}{y} f Fx Fy = x ◂ Fx ≤ f* f Fy
  Cᴰ .idᴰ = eqTo≤  (sym f*id)
  Cᴰ ._⋆ᴰ_ {f = f} {g} = seq* f g
  Cᴰ .⋆IdLᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆IdRᴰ fᴰ = toPathP (isProp≤ _ fᴰ)
  Cᴰ .⋆Assocᴰ _ _ _ = toPathP (isProp≤ _ _)
  Cᴰ .isSetHomᴰ = isProp→isSet isProp≤ 

module ConvertLogic
  {Σ : Signature}
  (M : CBPVModel Σ)
  (L : Logic M) where 

  open import HyperDoc.Syntax
  open CBPVModel M 
  open Logic L
  
  Vᴰ : Categoryᴰ V _ _ 
  Vᴰ = Convert.Cᴰ VH

  Cᴰ : Categoryᴰ C _ _ 
  Cᴰ = Convert.Cᴰ CH
  
  module VL = HDSyntax VH 
  module CL = HDSyntax CH 
  
  open MonFun renaming (f to fun)

  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (ALGᴰ {Σ})
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .Carrierᴰ M = A VL.◂ P ≤ (pull M $ Q) , isProp→isSet VL.isProp≤
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .interpᴰ op args dargs = pullOp op args P Q dargs 
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .carmapᴰ h P≤h*Q = 
    VL.seq  P'≤f*P (
    VL.seq (VL.mon* f P≤h*Q)  (
    VL.seq (VL.mon* f (pull h .isMon  Q≤g*Q')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (f , g)) h))))))
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {f , g} {P , Q} {P' , Q'} (P'≤f*P , Q≤g*Q') .presᴰ op args dargs = toPathP (VL.isProp≤ _ _)
  Oᴰ .Functorᴰ.F-idᴰ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)
  Oᴰ .Functorᴰ.F-seqᴰ _ _ = toPathP (AlgHomᴰ≡Prop λ _ → VL.isProp≤)

  OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor O) (Vᴰ ^opᴰ) Cᴰ (ALGᴰ {Σ})
  OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ

  Mᴰ : CBPVModelᴰ M 
  Mᴰ .CBPVModelᴰ.Vᴰ = Vᴰ
  Mᴰ .CBPVModelᴰ.Cᴰ = Cᴰ
  Mᴰ .CBPVModelᴰ.Oᴰ = Oᴰ

  open CBPVModelᴰ Mᴰ hiding (Vᴰ ; Cᴰ ; Oᴰ)

    -- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
  open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
  open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
  open import Cubical.Categories.Presheaf.More
  open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
  open import Cubical.Categories.Presheaf.Representable.More
  open import Cubical.Relation.Binary.Preorder
  open PreorderStr

  open import HyperDoc.CBPV.TypeStructure
  open import HyperDoc.CBPV.DisplayedTypeStructure

  open TypeStructure M
  open import HyperDoc.Connectives.Connectives
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  module test
    (hasO+ : HasO+)
    (V∨ : L∨.Has∨ VH) where 
          
    open DisplayedCoproducts hasO+ Mᴰ

    open +Syntax hasO+
          
    open L∨.HA renaming (_∨_ to _⋁_)
    module _ 
      (opLiftσ₁ : ((A A' : ob V) → HasLeftAdj (VH .F-hom (σ₁ {A}{A'}))))
      (opLiftσ₂ : ((A A' : ob V) → HasLeftAdj (VH .F-hom (σ₂ {A}{A'})))) where 

      _⋁ⱽ_ : {A : ob V} → Vᴰ .ob[_] A → Vᴰ .ob[_] A → Vᴰ .ob[_] A 
      _⋁ⱽ_ {A} = _⋁_  (V∨ .fst  A)

      ⋁ⱽ-intro₁ : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
        A VL.◂ P ≤ (P ⋁ⱽ Q)
      ⋁ⱽ-intro₁ {A}{P}{Q} = (or-intro1 (V∨ .fst A) {P = P}{P}{Q}VL.id⊢)

      ⋁ⱽ-intro₂ : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
        A VL.◂ Q ≤ (P ⋁ⱽ Q)
      ⋁ⱽ-intro₂ {A}{P}{Q} = (or-intro2 (V∨ .fst A) {P = Q}{P}{Q}VL.id⊢)


      ⋁ⱽ-elim : {A  : ob V}{P R Q : Vᴰ .ob[_] A} → 
        A VL.◂ P ≤ R  → 
        A VL.◂ Q ≤ R  →
        A VL.◂ (P ⋁ⱽ Q) ≤ R 
      ⋁ⱽ-elim {A} = or-elim (V∨ .fst A)

      _⋁ᴰ_ : {A A' : ob V} → Vᴰ .ob[_] A → Vᴰ .ob[_] A' → Vᴰ .ob[_] (A + A')  
      _⋁ᴰ_ {A}{A'} P Q = 
          _⋁_ 
            (V∨ .fst (A + A')) 
            (opLiftσ₁ A A' .fst $ P) 
            (opLiftσ₂ A A' .fst $ Q)
          
      proj₁ : {A A' : ob V}{P : Vᴰ .ob[_] A}{Q : Vᴰ .ob[_] A' }{R : Vᴰ .ob[_] (A + A') } → 
        (A + A') VL.◂ P ⋁ᴰ Q ≤ R → 
        (A + A') VL.◂ (opLiftσ₁ A A' .fst $ P) ≤ R
      proj₁ prf = VL.seq ⋁ⱽ-intro₁ prf
      
      ⋁ᴰ-intro₁ : {A A' : ob V}{P : Vᴰ .ob[_] A}{Q : Vᴰ .ob[_] A' } → 
        Vᴰ .Hom[_][_,_] σ₁ P  (P ⋁ᴰ Q)
      ⋁ᴰ-intro₁ {A}{A'}{P}{Q}= LtoR ⋁ⱽ-intro₁ where 
        open AdjSyntax (opLiftσ₁ A A')

      ⋁ᴰ-intro₁' : {A A' A'' : ob V} 
        {P : Vᴰ .ob[_] A}{Q : Vᴰ .ob[_] A' }{R : Vᴰ .ob[_] A'' }
        {f : V [ A + A' , A'' ]} → 
        Vᴰ .Hom[_][_,_] f (P ⋁ᴰ Q) R → 
        Vᴰ .Hom[_][_,_] (σ₁' f) P R 
      ⋁ᴰ-intro₁' {A}{A'}{A''}{P}{Q}{R}{f} prf = goal where 
        open AdjSyntax (opLiftσ₁ A A') 

        have : A VL.◂ P ≤ VL.f* (σ₁ ⋆⟨ V ⟩ f) R
        have = VL.seq (LtoR (proj₁ prf)) (VL.eqTo≤ (sym  VL.f*seq))

        goal : A VL.◂ P ≤ VL.f* (σ₁' f) R
        goal = VL.seq have (VL.eqTo≤ (cong (λ h → (VH .F-hom h) $ R) (sym(σ₁Sub f))))

      ⋁ᴰ-intro₂ : {A A' : ob V}{P : Vᴰ .ob[_] A}{Q : Vᴰ .ob[_] A' } → 
        Vᴰ .Hom[_][_,_] σ₂  Q  (P ⋁ᴰ Q)
      ⋁ᴰ-intro₂ {A}{A'}{P}{Q} = LtoR ⋁ⱽ-intro₂ where 
        open AdjSyntax (opLiftσ₂ A A')

      ⋁ᴰ-elim : {A A' A'' : ob V}{P : Vᴰ .ob[_] A}{Q : Vᴰ .ob[_] A'}{R : Vᴰ .ob[_] A'' }
        {f : V [ A , A'' ]}{g : V [ A' , A'' ]} → 
        Vᴰ .Hom[_][_,_]  f  P  R  → 
        Vᴰ .Hom[_][_,_] g  Q  R  → 
        Vᴰ .Hom[_][_,_] (caseV f g)  (P ⋁ᴰ Q)   R 
      ⋁ᴰ-elim {A}{A'}{A''}{P}{Q}{R}{f}{g} prf₁ prf₂ = goal where 
        module adj₁ = AdjSyntax (opLiftσ₁ A A')
        module adj₂ = AdjSyntax (opLiftσ₂ A A')

        have : A VL.◂ P  ≤ VL.f* σ₁ (VL.f* (caseV f g) R)
        have = VL.seq prf₁ (VL.eqTo≤  (cong (λ h → VL.f* h R) (sym (+β₁ f g)) ∙ VL.f*seq))

        have' : A' VL.◂ Q  ≤ VL.f* σ₂ (VL.f* (caseV f g) R)
        have' = VL.seq prf₂ (VL.eqTo≤ (cong (λ h → VL.f* h R) (sym (+β₂ f g)) ∙ VL.f*seq))

        goal : (A + A') VL.◂ P ⋁ᴰ Q ≤ VL.f* (caseV f g) R
        goal = 
          ⋁ⱽ-elim {A + A'}{adj₁.L $ P}{VL.f* (caseV f g) R}{adj₂.L $ Q} 
            (adj₁.RtoL have) 
            (adj₂.RtoL have')

      open import Cubical.Categories.Displayed.Presheaf.Morphism
      open PshHomᴰ
      open import Cubical.Foundations.Equiv.Dependent
      open import Cubical.Data.Sigma
      hasOᴰ+ : HasOᴰ+ 
      hasOᴰ+ P Q .fst = P ⋁ᴰ Q
      hasOᴰ+ {A}{A'} P Q .snd .fst .N-obᴰ {inl A''}{R}{f} prf = ⋁ᴰ-intro₁' prf , {!   !}
      hasOᴰ+ {A}{A'} P Q .snd .fst .N-obᴰ {inr B}{R}{f} prf = goal , {!   !} where 
        open AdjSyntax (opLiftσ₁ A A')
        _ : O'[ A + A' , B ]
        _ = f 
        have : (A + A') VL.◂ P ⋁ᴰ Q ≤ (pull f $ R) 
        have = prf

        have' : A VL.◂ (pull (σ₁c f) $ R) ≤ ((pull (lcomp σ₁ .carmap f) $ R))
        have' = VL.eqTo≤ (cong (λ h → (pull h $ R))  (σ₁cSub f))

        have''  : A VL.◂  ((pull (lcomp σ₁ .carmap f) $ R)) ≤ VL.f* σ₁ (pull f $ R) 
        have'' = VL.eqTo≤ (cong (λ h → h $ R) (pullLComp σ₁ f))

        sub : A VL.◂ P ≤ VL.f* σ₁ (pull f $ R)
        sub  = LtoR (proj₁ have)
        
        goal : A VL.◂ P ≤ (pull (σ₁c f) $ R)
        goal = VL.seq (LtoR (proj₁ have)) 
                (VL.eqTo≤ (sym (cong (λ h → h $ R) (pullLComp σ₁ f)) ∙ sym (cong (λ h → (pull h $ R))  (σ₁cSub f))) )
      hasOᴰ+ P Q .snd .fst .N-homᴰ {inl x} {inl x₁} = toPathP (ΣPathP (VL.isProp≤ _ _ , VL.isProp≤ _ _)) 
      hasOᴰ+ P Q .snd .fst .N-homᴰ {inr x} {inl x₁} = toPathP (ΣPathP (VL.isProp≤ _ _ , VL.isProp≤ _ _))
      hasOᴰ+ P Q .snd .fst .N-homᴰ {inr x} {inr x₁} = toPathP (ΣPathP (VL.isProp≤ _ _ , VL.isProp≤ _ _)) 
      hasOᴰ+ P Q .snd .snd {inl x} {R} .isIsoOver.inv (f , g) (prf , prf') = ⋁ᴰ-elim prf prf'
      hasOᴰ+ {A}{A'} P Q .snd .snd {inr B} {R} .isIsoOver.inv (f , g) (prf , prf') = goal where 
        module adj₁ = AdjSyntax (opLiftσ₁ A A')
        module adj₂ = AdjSyntax (opLiftσ₂ A A')

        _ : A VL.◂ P ≤ ((pull f) $ R)
        _ = prf

        eq1 : VL.f* σ₁ (pull (caseC f g) $ R) ≡ pull f $ R
        eq1 = cong (λ h → h $ R) (sym (pullLComp σ₁ (caseC f g))) 
          ∙ cong (λ h → pull h $ R) (sym  (σ₁cSub _ )∙ +βc₁ f g)

        eq2 : VL.f* σ₂ (pull (caseC f g) $ R) ≡ pull g $ R
        eq2 = cong (λ h → h $ R) (sym (pullLComp σ₂ (caseC f g))) 
          ∙ cong (λ h → pull h $ R) (sym  (σ₂cSub _ )∙ +βc₂ f g)

        goal : (A + A') VL.◂ P ⋁ᴰ Q ≤ (pull (caseC f g) $ R)
        goal = 
          ⋁ⱽ-elim {A + A'}{fun adj₁.L P}  
            (adj₁.RtoL (VL.seq prf (VL.eqTo≤ (sym eq1)))) 
            (adj₂.RtoL (VL.seq prf' (VL.eqTo≤ (sym eq2))))

      hasOᴰ+ P Q .snd .snd {inl x} {R} .isIsoOver.rightInv (f , g)(prf , prf') = 
        toPathP (ΣPathP ((VL.isProp≤ _ _) , (VL.isProp≤ _ _)))
      hasOᴰ+ P Q .snd .snd {inr x} {R} .isIsoOver.rightInv (f , g)(prf , prf') = 
        toPathP (ΣPathP ((VL.isProp≤ _ _) , (VL.isProp≤ _ _)))
      hasOᴰ+ P Q .snd .snd {inl x} {R} .isIsoOver.leftInv f prf = 
        toPathP (VL.isProp≤ _ _)
      hasOᴰ+ P Q .snd .snd {inr x} {R} .isIsoOver.leftInv f prf = 
        toPathP (VL.isProp≤ _ _)



  -- cartesian lifts over obliques
  -- except the displayed collage forgets the algebra structure on obliques..
  ForgetfulObliqueLifts : Type 
  ForgetfulObliqueLifts = {x y : Collage .ob} (f : Collage [ x , y ]) (yᴰ : ob[ Collageᴰ ] y) → CartesianLift  Collageᴰ {x}{y} f yᴰ 

  hasForgetfulObliqueLifts : ForgetfulObliqueLifts
  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .fst = VH .F-hom f .fun yᴰ
  hasForgetfulObliqueLifts {inl A} {inr x} M yᴰ .fst = pull M $ yᴰ
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .fst = CH .F-hom f .fun yᴰ

  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .snd .PshIso.trans .PshHom.N-ob (inl A'' , PA'' , A''→A) prf = 
    VL.seq prf (VL.eqTo≤ (cong (λ h → h $ yᴰ) (sym (VH .F-seq _ _))))
  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .snd .PshIso.trans .PshHom.N-hom (inl x , snd₁) (inl x₁ , snd₂) f' p = VL.isProp≤ _ _ 
  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .snd .PshIso.nIso (inl A'' , PA'' , A''→A) .fst prf = 
    VL.seq prf (VL.eqTo≤ ((cong (λ h → h $ yᴰ) (VH .F-seq _ _))))
  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .snd .PshIso.nIso (inl A'' , PA'' , A''→A) .snd .fst b = VL.isProp≤ _ _
  hasForgetfulObliqueLifts {inl A} {inl A'} f yᴰ .snd .PshIso.nIso (inl A'' , PA'' , A''→A) .snd .snd a = VL.isProp≤ _ _

  hasForgetfulObliqueLifts {inl A} {inr B} M yᴰ .snd .PshIso.trans .PshHom.N-ob (inl A' , PA' , V) prf = 
    VL.seq prf (VL.eqTo≤ (cong (λ h → h $ yᴰ) (sym ( pullLComp V M)))) 
  hasForgetfulObliqueLifts {inl A} {inr B} f yᴰ .snd .PshIso.trans .PshHom.N-hom (inl x , snd₁) (inl x₁ , snd₂) f' p = VL.isProp≤ _ _
  hasForgetfulObliqueLifts {inl A} {inr B} M yᴰ .snd .PshIso.nIso (inl A' , PA' , V) .fst prf = 
    VL.seq prf (VL.eqTo≤ ((cong (λ h → h $ yᴰ) (pullLComp V M)) ∙ cong {x = pull M} (λ h → fun (VH .F-hom V) (fun h yᴰ)) refl))
  hasForgetfulObliqueLifts {inl A} {inr B} f yᴰ .snd .PshIso.nIso (inl A' , PA' , A'→A) .snd .fst b = VL.isProp≤ _ _
  hasForgetfulObliqueLifts {inl A} {inr B} f yᴰ .snd .PshIso.nIso (inl A' , PA' , A'→A) .snd .snd a = VL.isProp≤ _ _
  
  hasForgetfulObliqueLifts {inr B} {inr B'} M yᴰ .snd .PshIso.trans .PshHom.N-ob (inl B'' , PB'' , S) prf = 
    VL.seq prf (VL.eqTo≤ (cong (λ h → h $ yᴰ) (sym ( pullRComp M S)) ) )
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.trans .PshHom.N-hom (inr x , snd₁) (inr x₁ , snd₂) f' p = CL.isProp≤ _ _
  hasForgetfulObliqueLifts {inr B} {inr B'} M yᴰ .snd .PshIso.nIso (inl B'' , PB'' , S) .fst prf = 
    VL.seq prf (VL.eqTo≤ ((cong (λ h → h $ yᴰ) (pullRComp M S)) ∙ cong {x = CH .F-hom M}(λ h → fun (N-ob Sq (B'' , B) S) (fun (h) yᴰ)) refl ))
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.nIso (inl B'' , PB'' , B''→B) .snd .fst b = VL.isProp≤ _ _
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.nIso (inl B'' , PB'' , B''→B) .snd .snd a = VL.isProp≤ _ _

  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.trans .PshHom.N-ob (inr B'' , PB'' , S) prf = 
    CL.seq prf ((CL.eqTo≤ (cong (λ h → h $ yᴰ) (sym (CH .F-seq _ _)))))
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.trans .PshHom.N-hom (inl x , snd₁) c' f' p = VL.isProp≤ _ _
  hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.trans .PshHom.N-hom (inr x , snd₁) c' f' p = CL.isProp≤ _ _
  hasForgetfulObliqueLifts {inr x₁} {inr x₂} M yᴰ .snd .PshIso.nIso (inr B'' , fst₁ , S) .fst prf = 
    CL.seq prf (CL.eqTo≤ ((cong (λ h → h $ yᴰ) (CH .F-seq _ _))))
  hasForgetfulObliqueLifts {inr x} {inr x₁} f yᴰ .snd .PshIso.nIso (inr x₂ , fst₁ , snd₁) .snd .fst b = CL.isProp≤ _ _
  hasForgetfulObliqueLifts {inr x} {inr x₁} f yᴰ .snd .PshIso.nIso (inr x₂ , fst₁ , snd₁) .snd .snd a = CL.isProp≤ _ _
  --hasForgetfulObliqueLifts {inr B} {inr B'} f yᴰ .snd .PshIso.nIso x = ?

module ModelSection 
  {Σ : Signature}
  {M N : CBPVModel Σ}
  (F : CBPVMorphism M N)
  (L : Logic N) where 

  open CBPVMorphism F
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
    module L = Logic L
    module VH' = HDSyntax (L.VH ∘F (FV ^opF))
    module CH' = HDSyntax (L.CH ∘F (FC ^opF))

  open ConvertLogic N L
  module _ 
    (SV : Section FV Vᴰ) 
    (SC : Section FC Cᴰ) where 

    private 
      module SV = Section SV 
      module SC = Section SC
    
    SectionO : Type 
    SectionO = 
      ∀ 
        {A : ob M.V}
        {B : ob M.C}
        (M : M.O'[ A , B ]) → 
        ⟨ Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B) .Carrierᴰ (FO .N-ob (A , B) .carmap M) ⟩
      
  CBPVSection : Type 
  CBPVSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

CBPVGlobalSection :  {Σ : Signature}{M : CBPVModel Σ} → Logic M → Type 
CBPVGlobalSection L = ModelSection.CBPVSection idCBPVMorphism L

module Reconstruct 
  {Σ : Signature}
  {M : CBPVModel Σ}
  {L : Logic M}
  (GS : CBPVGlobalSection L) 
  where 

  open CBPVModel M 
  open Logic L 
  open Section
  open ConvertLogic M L
  open import Cubical.Categories.Constructions.TotalCategory
  open HyperDoc.Algebra.Algebra
  open Alg

  open import Cubical.Data.Sigma hiding (Σ)

  ΣALG : Functor (∫C ALGᴰ) (ALG Σ) 
  ΣALG .F-ob (A , Aᴰ) .Carrier = (Σ[ a ∈ A .Carrier .fst ] Aᴰ .Carrierᴰ a .fst) , isSetΣ (A .Carrier .snd) λ a → Aᴰ .Carrierᴰ a .snd
  ΣALG .F-ob (A , Aᴰ) .interp op args = A .interp op (λ z → args z .fst) , Aᴰ .interpᴰ op (λ z → args z .fst) λ x → args x .snd
  ΣALG .F-hom {A , Aᴰ} {A' , A'ᴰ} (f , fᴰ) .carmap = λ z → f .carmap (z .fst) , fᴰ .carmapᴰ (z .fst) (z .snd)
  ΣALG .F-hom {A , Aᴰ} {A' , A'ᴰ} (f , fᴰ) .pres op args = ΣPathP (f .pres op (λ z → args z .fst) , fᴰ .presᴰ op (λ z → args z .fst) λ x → args x .snd)
  ΣALG .F-id = AlgHom≡ refl
  ΣALG .F-seq f g = AlgHom≡ refl

  conv : Functor ((∫C Vᴰ ^op) ×C ∫C Cᴰ) (∫C ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ))
  conv .F-ob ((A , Aᴰ),(B , Bᴰ)) = (A , B) , Aᴰ , Bᴰ 
  conv .F-hom = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
  conv .F-id = refl
  conv .F-seq _ _ = refl

  TotalModel : CBPVModel Σ 
  TotalModel .CBPVModel.V = ∫C Vᴰ
  TotalModel .CBPVModel.C = ∫C Cᴰ
  TotalModel .CBPVModel.O = ΣALG ∘F ∫F (Oᴰ) ∘F conv

  π : CBPVMorphism TotalModel M 
  π .CBPVMorphism.FV .F-ob = λ z → z .fst
  π .CBPVMorphism.FV .F-hom = λ z → z .fst
  π .CBPVMorphism.FV .F-id = refl
  π .CBPVMorphism.FV .F-seq _ _ = refl
  π .CBPVMorphism.FC .F-ob = λ z → z .fst
  π .CBPVMorphism.FC .F-hom = λ z → z .fst
  π .CBPVMorphism.FC .F-id = refl
  π .CBPVMorphism.FC .F-seq _ _ = refl
  π .CBPVMorphism.FO .N-ob x .carmap = λ z → z .fst
  π .CBPVMorphism.FO .N-ob x .pres op args = refl
  π .CBPVMorphism.FO .N-hom f = AlgHom≡  (funExt λ x → refl)

  GSFun : CBPVMorphism M TotalModel
  GSFun .CBPVMorphism.FV .F-ob A = A , F-obᴰ (GS .fst) A 
  GSFun .CBPVMorphism.FV .F-hom V = V , (F-homᴰ (GS .fst) V)
  GSFun .CBPVMorphism.FV .F-id = ΣPathP (refl , VL.isProp≤ _ _)
  GSFun .CBPVMorphism.FV .F-seq _ _  = ΣPathP (refl , VL.isProp≤  _ _)
  GSFun .CBPVMorphism.FC .F-ob B = B , F-obᴰ (GS .snd .fst) B
  GSFun .CBPVMorphism.FC .F-hom S = S , (F-homᴰ (GS .snd .fst) S)
  GSFun .CBPVMorphism.FC .F-id = ΣPathP (refl , CL.isProp≤ _ _)
  GSFun .CBPVMorphism.FC .F-seq _ _  = ΣPathP (refl , CL.isProp≤  _ _)
  GSFun .CBPVMorphism.FO .N-ob (A , B) .carmap M = M , GS .snd .snd M
  GSFun .CBPVMorphism.FO .N-ob (A , B) .pres op args = ΣPathP (refl , VL.isProp≤ _ _)
  GSFun .CBPVMorphism.FO .N-hom (V , S) = AlgHom≡ (funExt λ M → ΣPathP (refl , VL.isProp≤ _ _))
