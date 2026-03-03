{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.Logic.Base where

open import Cubical.Data.FinData

open import Cubical.Foundations.Prelude
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
