{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Logic where 

open import Cubical.Data.Sigma
open import Cubical.Data.FinData
open import Cubical.Data.Unit 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Bifunctor 
open import Cubical.Categories.Bifunctor hiding (Sym)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint

open import HyperDoc.Operational.Effects.Model 
open import HyperDoc.Lib
open import HyperDoc.Syntax
open import HyperDoc.Algebra.Algebra using(Signature)
open import HyperDoc.Operational.Effects.BiAlgebra
open import HyperDoc.Operational.Effects.TypeStructure

open BifunctorSep
open BifunctorSepᴰ
open BiAlg hiding (Edge[_,_])
open BiAlgHom
open Categoryᴰ
open Category 
open Functor 
open NatTrans 
open NatTransᴰ
open Signature

module _ 
  {Sig : Signature}
  (M : CBPVModel Sig) where

  open CBPVModelSyntax M

  
  Hom^op : {ℓL : Level } →  Functor ((POSET ℓL ℓL) ×C (POSET ℓL ℓL)^op) (SET ℓL )
  Hom^op = (HomFunctor _) ∘F Sym

  record CBPVLogic : Type where 
    field 
      LV : Functor (V ^op) (POSET _ _)
      LC : Functor (C ^op) (POSET _ _)
      LSq : NatTrans (FORGET ∘F OPar) (Hom^op  ∘F (LV ×F ((LC ^opF) ∘F to^op^op )))

    module LV = HDSyntax LV
    module LC = HDSyntax LC

    pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
      → MonFun (F-ob LC B .fst) (F-ob LV A .fst)
    pull {A} {B} M = LSq .N-ob (A , B) M

    field 
      antired : ∀ {A B Q}{M M' : O'[ A , B ]} → 
        Edge[ M , M' ] → 
        A LV.◂ (pull M' $ Q) ≤ (pull M $ Q)
      pullOp : 
        {A : V .ob}{B : C .ob}
        (op : Op Sig)
        (args : (Fin (arity Sig op) → O'[ A , B ]))
        (P : LV.F∣ A ∣)(Q : LC.F∣ B ∣)
        (dargs : (x : Fin (arity Sig op)) → A LV.◂ P ≤ (pull (args x) $ Q))→ 
        A LV.◂ P ≤ (pull (interp op args) $ Q) 

    pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull  (OPar .F-hom (V , S) .map M) ≡ MonComp (LC .F-hom S) (MonComp (pull M) (LV .F-hom V))
    pullComp V S M = funExt⁻ (LSq .N-hom (V , S)) M

    pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
      pull (O .Bif-homL V B .map M) ≡ MonComp (pull M) (LV .F-hom V)
    pullLComp V M = {!   !}
      {-}  pullComp V (C .id) M
      ∙ cong
          (λ h → MonComp h (MonComp (pull M) (LV .F-hom V)))
          (LC .F-id)  !}
          -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)
          -- Bif-L-id
          -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)
          -}

    pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
      pull (O .Bif-homR A S .map M) ≡ MonComp (LC .F-hom S) (pull M)
    pullRComp S M = {!   !}
      -- eqMon _ _  (funExt λ Q' → λ i → {! LSq .N-hom (V .id , S) i M .MonFun.f Q'  !})
      -- pullComp (V .id) S M ∙ cong₂ MonComp refl (LV .F-id)

    V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣}  → 
      A LV.◂ LV.f* V (pull M $ Q) ≤ (pull (O .Bif-homL V B .map M) $ Q) 
    V*M*→VM* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

    VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣} →  
      A LV.◂ (pull (O .Bif-homL V B .map M) $ Q) ≤ LV.f* V (pull M $ Q)
    VM*→V*M* = LV.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

    MS*→M*S*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
      A LV.◂ pull (O .Bif-homR A S .map M) $ Q' ≤ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q'
    MS*→M*S* = LV.eqTo≤ (cong₂ MonFun.f (pullRComp _ _ ) refl)

    M*S*→MS*  : ∀ {A B B'}{S : C [ B , B' ]}{M : O'[ A , B ]}{Q' : LC.F∣ B' ∣} →  
      A LV.◂ MonFun.f (MonComp (LC .F-hom S) (pull M)) Q' ≤ (pull (O .Bif-homR A S .map M) $ Q')
    M*S*→MS* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullRComp _ _ )) refl)

    proofLcomp : ∀ {A A' B P P' Q V M} → 
      A' LV.◂ P' ≤ LV.f* V P → 
      A LV.◂ P ≤ (pull {B = B} M $ Q) → 
      ---------------------------
      A' LV.◂ P' ≤ (pull (O .Bif-homL V _ .map M) $ Q)
    proofLcomp {V = V} P'≤VP P≤MQ = LV.seq P'≤VP (LV.seq (LV.mon* V P≤MQ) V*M*→VM*)

    proofRcomp : ∀ {A B B' P Q Q' S M} → 
      A LV.◂ P ≤ (pull {B = B} M $ Q) → 
      B LC.◂ Q ≤ LC.f* {c' = B'} S Q' → 
      ---------------------------
      A LV.◂ P ≤ (pull (O .Bif-homR _ S .map M) $ Q')
    proofRcomp  {M = M}P≤MQ Q≤SQ' = LV.seq P≤MQ (LV.seq (pull M .MonFun.isMon  Q≤SQ') M*S*→MS*)



module Convert {C : Category _ _} (F : Functor (C ^op) (POSET _ _ )) where 
  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open Categoryᴰ
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
  {Sig : Signature}
  {M : CBPVModel Sig}
  (L : CBPVLogic M) where 
  open CBPVModelSyntax M 
  open CBPVLogic L

  open BiAlgᴰ
  Vᴰ = Convert.Cᴰ (LV)
  Cᴰ = Convert.Cᴰ (LC)

  bialgᴰ : ∀ {A B}(P : Vᴰ .ob[_] A)(Q : Cᴰ .ob[_] B) → BiAlgᴰ (O .Bif-ob A B) 
  bialgᴰ {A} {B} P Q .carᴰ M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤
  bialgᴰ {A} {B} P Q .isAlgᴰ op args dargs = pullOp {A}{B} op args P Q dargs
  -- not used in cannonicity
  bialgᴰ {A} {B} P Q .isRGraphᴰ .fst _ _ _ = Unit , isPropUnit
  bialgᴰ {A} {B} P Q .isRGraphᴰ .snd = λ xᴰ → tt
  bialgᴰ {A} {B} P Q .congruenceᴰ = λ op args args' edges dargs dargs' edgesᴰ → tt

  leftActionᴰ : ∀ {A A' B}{P : Vᴰ .ob[_] A}{P' : Vᴰ .ob[_] A'}{Q : Cᴰ .ob[_] B}
    (V : V [ A' , A ])
    (φ : (Vᴰ ^opᴰ) [ V ][ P , P' ]) → 
    BIALGᴰ [ O .Bif-homL V B ][ bialgᴰ P Q , bialgᴰ P' Q ] 
  leftActionᴰ V φ .BiAlgHomᴰ.mapᴰ M ψ = proofLcomp φ ψ
  leftActionᴰ V φ .BiAlgHomᴰ.isAlgHomᴰ op args dargs = toPathP (LV.isProp≤  _ _)
  leftActionᴰ V φ .BiAlgHomᴰ.isRelatorᴰ .fst = λ nᴰ n'ᴰ _ → tt
  leftActionᴰ V φ .BiAlgHomᴰ.isRelatorᴰ .snd = refl

  rightActionᴰ : ∀ {A B B'}{P : Vᴰ .ob[_] A}{Q : Cᴰ .ob[_] B}{Q' : Cᴰ .ob[_] B'}
    (S : C [ B , B' ]) → 
    (φ : Cᴰ [ S ][ Q , Q' ]) → 
    BIALGᴰ [ O .Bif-homR A S  ][ bialgᴰ P Q , bialgᴰ P Q' ] 
  rightActionᴰ S φ .BiAlgHomᴰ.mapᴰ M ψ = proofRcomp ψ φ
  rightActionᴰ S φ .BiAlgHomᴰ.isAlgHomᴰ op args dargs = toPathP (LV.isProp≤  _ _)
  rightActionᴰ S φ .BiAlgHomᴰ.isRelatorᴰ .fst = λ nᴰ n'ᴰ _ → tt
  rightActionᴰ S φ .BiAlgHomᴰ.isRelatorᴰ .snd = refl

  Oᴰ : BifunctorSepᴰ O (Vᴰ ^opᴰ) Cᴰ BIALGᴰ
  Oᴰ .Bif-obᴰ {A}{B} = bialgᴰ
  Oᴰ .Bif-homLᴰ {f = V} φ _ = leftActionᴰ V φ
  Oᴰ .Bif-L-idᴰ = {!   !}
  Oᴰ .Bif-L-seqᴰ = {!   !}
  Oᴰ .Bif-homRᴰ {g = S} φ _ = rightActionᴰ S φ
  Oᴰ .Bif-R-idᴰ = {!   !}
  Oᴰ .Bif-R-seqᴰ = {!   !}
  Oᴰ .SepBif-RL-commuteᴰ = {!   !}

  Mᴰ : CBPVModelᴰ M 
  Mᴰ .fst = Vᴰ
  Mᴰ .snd .fst = Cᴰ
  Mᴰ .snd .snd = Oᴰ

module LogicStruct 
  {Sig : Signature}
  {M : CBPVModel Sig}
  (L : CBPVLogic M) where 

  open CBPVLogic L
  open CBPVModelSyntax M
  open import HyperDoc.Connectives.Connectives

  Has𝟙ᴸ : Type 
  Has𝟙ᴸ = L⊤.Has⊤ LV

  Has+ᴸ : Type 
  Has+ᴸ = L∨.Has∨ LV × L∃.Has∃ LV 

  HasFTyᴸ : Type 
  HasFTyᴸ = ({A : ob V}{B : ob C}(M : O'[ A , B ]) → HasLeftAdj (pull M))


module Reindex
  {Sig : Signature}
  {M N : CBPVModel Sig}
  (F : CBPVMorphism M N)
  (L : CBPVLogic N) where 
  private 
    module M = CBPVModelSyntax M
    module N = CBPVModelSyntax N
    module F = CBPVMorphismSyntax F 
    module L = CBPVLogic L
    module TSM = TypeStructure M
    module TSN = TypeStructure N


  open CBPVMorphismSyntax F

  LV' : Functor (M.V ^op) (POSET ℓ-zero ℓ-zero) 
  LV' = L.LV ∘F (FV ^opF)

  LC' : Functor (M.C ^op) (POSET ℓ-zero ℓ-zero) 
  LC' = L.LC ∘F (FC ^opF)

  LSq' : NatTrans (FORGET ∘F M.OPar) (Hom^op M ∘F (LV' ×F ((LC' ^opF) ∘F to^op^op)))
  LSq' = seqTrans (FORGET ∘ʳ FO) (seqTrans (F-assocl {F = (F.FV  ^opF) ×F F.FC}{N.OPar}{FORGET}) (seqTrans (L.LSq ∘ˡ ((FV ^opF) ×F FC)) dumb)) where 
    dumb : 
      NatTrans
      ((Hom^op N ∘F (L.LV ×F ((L.LC ^opF) ∘F to^op^op))) ∘F
      ((FV ^opF) ×F FC))
      (Hom^op M ∘F (LV' ×F ((LC' ^opF) ∘F to^op^op)))
    dumb .N-ob x z = z
    dumb .N-hom _ = refl

  reindex : CBPVLogic M 
  reindex .CBPVLogic.LV = LV'
  reindex .CBPVLogic.LC = LC'
  reindex .CBPVLogic.LSq = LSq'
  reindex .CBPVLogic.antired = λ z → L.antired (N-ob (F .snd .snd) (_ , _) .isRelator .fst z)
  reindex .CBPVLogic.pullOp = {!   !}
  {-
  {A}{B} op args P Q dargs = goal where 
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

  -}

  module L' = CBPVLogic reindex

  module LS = LogicStruct L 
  module LS' = LogicStruct reindex

  pres𝟙ᴸ  : LS.Has𝟙ᴸ → LS'.Has𝟙ᴸ
  pres𝟙ᴸ has𝟙ᴸ = (λ c → has𝟙ᴸ .fst (F-ob (FV ^opF) c)) ,
    (λ {c} {c'} f → has𝟙ᴸ .snd (F-hom (FV ^opF) f))
  
  pres+ᴸ  : LS.Has+ᴸ → LS'.Has+ᴸ
  pres+ᴸ has+ᴸ = ((λ c → has+ᴸ .fst .fst (F-ob (FV ^opF) c)) ,
     (λ {c} {c'} f → has+ᴸ .fst .snd (F-hom (FV ^opF) f)))
    , (λ {A} {A'} f → has+ᴸ .snd (F-hom (FV ^opF) f))

  presFTyᴸ  : LS.HasFTyᴸ → LS'.HasFTyᴸ
  presFTyᴸ hasFTyᴸ {A}{B} M = hasFTyᴸ (N-ob F-assocl (A , B) (N-ob (FORGET ∘ʳ FO) (A , B) M))



module LogicalToDisplayed 
  {Sig : Signature}
  {M : CBPVModel Sig}
  (L : CBPVLogic M) where 
  open import HyperDoc.Connectives.Connectives

  open LogicStruct L
  open TypeStructure M
  open CBPVLogic L
  open CBPVModelSyntax M
  open ConvertLogic L
  open TypeStructureᴰ Mᴰ
  open WkRepresentationᴰ

  module 𝟙TyDep (has𝟙 : Has𝟙)(has𝟙ᴸ : Has𝟙ᴸ) where 
    open L⊤
    open HA 
    has𝟙ᴰ : Has𝟙ᴰ has𝟙 
    has𝟙ᴰ .fst = top (has𝟙ᴸ .fst (has𝟙 .fst))
    has𝟙ᴰ .snd .N-obᴰ {A} P tt tt = goal where 
      goal : A LV.◂ P ≤ LV.f* (N-ob (has𝟙 .snd) A tt) (has𝟙ᴰ .fst)
      goal = LV.seq (top-top (has𝟙ᴸ .fst A)) {! has𝟙ᴸ .snd  !} -- use preservation of top by reindexing
    has𝟙ᴰ .snd .N-homᴰ {A}{A'}{V}{P}{P'} P'≤VP = toPathP (funExt λ _ → funExt λ _ → LV.isProp≤ _ _)

  module FTyDep (hasFTy : HasFTy) (hasFTyᴸ : HasFTyᴸ) where
    open FTySyntax hasFTy 

    hasFTyᴰ : HasFTyᴰ hasFTy 
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.repᴰ = hasFTyᴸ (ret (C .id)) .fst $ Aᴰ
    hasFTyᴰ {A} Aᴰ .WkRepresentationᴰ.fwdᴰ .N-obᴰ {B} Bᴰ S FᴰAᴰ≤retAᴰ = goal where 
      open AdjSyntax (hasFTyᴸ  (ret (C .id))) 
      goal : A  LV.◂ Aᴰ ≤ (pull (ret S) $ Bᴰ) 
      goal = LV.seq (LtoR FᴰAᴰ≤retAᴰ) (LV.eqTo≤ {!   !}) -- fun (pull (ret (C .id))) (LC.f* S Bᴰ) ≡ fun (pull (ret S)) Bᴰ
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasFTyᴰ {A} Aᴰ .WkRepresentationᴰ.bkwdᴰ {B}{Bᴰ}{M} Aᴰ≤MBᴰ = goal where 
      open AdjSyntax (hasFTyᴸ  (ret (C .id))) 
      goal : F A  LC.◂ hasFTyᴸ (ret (C .id)) .fst $ Aᴰ ≤ LC.f* (bind M) Bᴰ 
      goal = RtoL (LV.seq Aᴰ≤MBᴰ (LV.seq (antired (subst (λ h → Edge[ h , M ]) {!   !}  (Fβ M))) MS*→M*S*))
    hasFTyᴰ Aᴰ .WkRepresentationᴰ.wkretractᴰ e = tt 

  module +TyDep (has+ : Has+)((has+ᴸ , has∃ᴸ ) : Has+ᴸ ) where 
    open import Cubical.Categories.Instances.Preorders.Monotone
    open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
    open MonFun renaming (f to fun)
    --open +TySyntax has+
    open L∨
    open L∃ 
    open ∃Syntax {L = LV} has∃ᴸ
    open HA renaming (_∨_ to _∨ⱽ_)
    open Has+' 


    _⋁ⱽ_ : {A : ob V} → LV.F∣ A ∣ → LV.F∣ A ∣ →   LV.F∣ A ∣
    _⋁ⱽ_ {A} = _∨ⱽ_ {P = LV .F-ob A}(has+ᴸ .fst A) 

    ⋁ⱽ-intro₁ : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ (P ⋁ⱽ Q)
    ⋁ⱽ-intro₁ {A}{P}{Q} = or-intro1 ((has+ᴸ .fst A)) {P = P}{P}{Q} LV.id⊢

    ⋁ⱽ-intro₂  : {A  : ob V}{P Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ (Q ⋁ⱽ P)
    ⋁ⱽ-intro₂ {A}{P}{Q} = or-intro2 ((has+ᴸ .fst A)) {P = P}{Q}{P} LV.id⊢


    ⋁ⱽ-elim : {A  : ob V}{P R Q : Vᴰ .ob[_] A} → 
      A LV.◂ P ≤ R  → 
      A LV.◂ Q ≤ R  →
      A LV.◂ (P ⋁ⱽ Q) ≤ R 
    ⋁ⱽ-elim {A} = or-elim  (has+ᴸ .fst A)

    _⋀ᴰ_ : {A A' : ob V} → LV.F∣ A ∣ → LV.F∣ A' ∣ → LV.F∣ A+A' (has+ A A') ∣ 
    _⋀ᴰ_ {A}{A'} P P' = ∃f {f = σ₁ ((has+ A A'))} P ⋁ⱽ ∃f {f = σ₂ ((has+ A A'))} P'

    has+ᴰ : Has+ᴰ has+
    has+ᴰ Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.Aᴰ+A'ᴰ = Aᴰ ⋀ᴰ A'ᴰ
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.matchᴰ .N-obᴰ {B} Bᴰ (M , N) (Aᴰ≤MBᴰ , A'ᴰ≤NBᴰ)  = goal where 
      module adj₁ =  AdjSyntax (has∃ᴸ (σ₁ (has+ A A')))
      module adj₂ =  AdjSyntax (has∃ᴸ (σ₂ (has+ A A')))

      sub1 : A LV.◂  Aᴰ ≤ LV.f* (σ₁ (has+ A A')) (pull (match (has+ A A') .N-ob B (M , N)) $ Bᴰ) 
      sub1 = LV.seq Aᴰ≤MBᴰ (LV.seq (antired (+β₁ (has+ A A') M N)) VM*→V*M*)

      sub2 : A' LV.◂  A'ᴰ ≤ LV.f* (σ₂ (has+ A A')) (pull (match (has+ A A') .N-ob B (M , N)) $ Bᴰ) 
      sub2 = LV.seq A'ᴰ≤NBᴰ (LV.seq (antired (+β₂ (has+ A A') M N)) VM*→V*M*)

      goal : (A+A' (has+ A A')) LV.◂ Aᴰ ⋀ᴰ A'ᴰ ≤ (pull (match ((has+ A A')) .N-ob  B (M , N)) $ Bᴰ)
      goal =  ⋁ⱽ-elim {TypeStructure.Has+'.A+A' (has+ A A')}{fun adj₁.L Aᴰ}{fun (pull (N-ob (TypeStructure.Has+'.match (has+ A A')) B (M , N)))
        Bᴰ}{fun adj₂.L A'ᴰ} (adj₁.RtoL sub1) (adj₂.RtoL sub2)
    has+ᴰ Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.matchᴰ .N-homᴰ _ = funExt λ _ → funExt λ _ → toPathP (LV.isProp≤ _ _)
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.σ₁ᴰ = goal where 
      open AdjSyntax (has∃ᴸ (σ₁ (has+ A A')))
      goal : A LV.◂ Aᴰ ≤ LV.f* (σ₁ (has+ A A'))  (Aᴰ ⋀ᴰ A'ᴰ) 
      goal = LtoR ⋁ⱽ-intro₁
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.σ₂ᴰ = goal where 
      open AdjSyntax (has∃ᴸ (σ₂ (has+ A A')))
      goal : A' LV.◂ A'ᴰ ≤ LV.f* (σ₂ (has+ A A')) (Aᴰ ⋀ᴰ A'ᴰ) 
      goal = LtoR ⋁ⱽ-intro₂
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.+β₁ᴰ {B}{Bᴰ}{M}{M'}{e} Aᴰ≤MBᴰ A'ᴰ≤M'Bᴰ = tt
      -- edge-1 {! anti !} _ Aᴰ≤MBᴰ
    has+ᴰ {A}{A'} Aᴰ A'ᴰ .TypeStructureᴰ.Has+'ᴰ.+β₂ᴰ {B}{Bᴰ}{M}{M'}{e} Aᴰ≤MBᴰ A'ᴰ≤M'Bᴰ = tt

  module UTyDep (hasUTy : HasUTy) where 

    open UTySyntax hasUTy
    {- holes dispatched with naturality
        force (subV V W) ≡ subC V (force W) -}
    hasUTyᴰ : HasUTyᴰ hasUTy
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.repᴰ = pull (force (V .id)) $ Bᴰ
    hasUTyᴰ {B} Q .WkRepresentationᴰ.fwdᴰ .N-obᴰ {A} P V P≤!VQ = LV.seq P≤!VQ (LV.seq V*M*→VM* {!   !}) -- pull (subC V (force id)) ≡ pull (force V)
    hasUTyᴰ Bᴰ .WkRepresentationᴰ.fwdᴰ .N-homᴰ _ = toPathP (funExt λ x → funExt λ y → LV.isProp≤  _ _)
    hasUTyᴰ {B} Q .WkRepresentationᴰ.bkwdᴰ {A}{P} {M} P≤MQ = LV.seq P≤MQ (LV.seq (LV.seq (antired (Uβ M)) (LV.eqTo≤ {!   !})) VM*→V*M*)  -- pull (force (thunk M)) ≡ pull (subC (thunk M) (force id))
    hasUTyᴰ {B} Q .WkRepresentationᴰ.wkretractᴰ {A}{P}{M} P≤MQ = tt

