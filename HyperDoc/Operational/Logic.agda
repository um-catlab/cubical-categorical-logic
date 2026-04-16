{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Logic where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Bifunctor 
open import Cubical.Categories.Bifunctor hiding (Sym)


open import HyperDoc.Operational.Model 
open import HyperDoc.Operational.Graph
open import HyperDoc.Lib

open BifunctorSep
open Category 
open Functor 
open NatTrans 

module _ 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' : Level}
  (M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG') where

  open CBPVModelSyntax M

  
  Hom^op : {ℓL : Level } →  Functor ((POSET ℓL ℓL) ×C (POSET ℓL ℓL)^op) (SET ℓL )
  Hom^op = (HomFunctor _) ∘F Sym

  CBPVLogic : (ℓL : Level  ) →  Type _ 
  CBPVLogic ℓL  = 
    Σ[ LV ∈ Functor (V ^op) (POSET ℓL ℓL) ] 
    Σ[ LC ∈ Functor (C ^op) (POSET ℓL ℓL) ] 
    Σ[ LSq ∈ NatTrans (FORGET ∘F OPar) (Hom^op  ∘F (LV ×F ((LC ^opF) ∘F to^op^op ))) ] 
    {!   !}

module CBPVLogicSyntax 
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  (L : CBPVLogic M ℓL ) where 

  open CBPVModelSyntax M

  LV = L .fst 
  LC = L .snd .fst 
  LSq = L .snd .snd .fst

  open import HyperDoc.Syntax
  module LC = HDSyntax LC
  module LV = HDSyntax LV

  pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
    → MonFun (F-ob LC B .fst) (F-ob LV A .fst)
  pull {A} {B} M = LSq .N-ob (A , B) M

  pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (OPar .F-hom (V , S) .fst M) ≡ MonComp (LC .F-hom S) (MonComp (pull M) (LV .F-hom V))
  pullComp V S M = funExt⁻ (LSq .N-hom (V , S)) M

  pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
    pull (O .Bif-homL V B .fst M) ≡ MonComp (pull M) (LV .F-hom V)
  pullLComp V M = {!   !}
    -- Bif-L-id
    -- pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (LV .F-hom V))) (LC .F-id)

  pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (O .Bif-homR A S .fst M) ≡ MonComp (LC .F-hom S) (pull M)
  pullRComp S M = {!   !}
    -- pullComp (V .id) S M ∙ cong₂ MonComp refl (LV .F-id)

  V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣}  → 
    A LV.◂ LV.f* V (pull M $ Q) ≤ (pull (O .Bif-homL V B .fst M) $ Q) 
  V*M*→VM* = LV.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

  VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : LC.F∣ B ∣} →  
    A LV.◂ (pull (O .Bif-homL V B .fst M) $ Q) ≤ LV.f* V (pull M $ Q)
  VM*→V*M* = LV.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

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
  {ℓV ℓV' ℓC ℓC' ℓG ℓG' ℓL : Level}
  {M : CBPVModel ℓV ℓV' ℓC ℓC' ℓG ℓG'}
  (L : CBPVLogic M ℓL ) where 

  open import HyperDoc.Syntax
  open import Cubical.Categories.Displayed.Base 
  open import Cubical.Categories.Displayed.Functor
  open import Cubical.Categories.Displayed.BinProduct
  open import Cubical.Categories.Bifunctor

  open Bifunctor
  open Categoryᴰ
  open Functorᴰ

  Vᴰ = Convert.Cᴰ (L .fst)
  Cᴰ = Convert.Cᴰ (L .snd .fst)

    
  open CBPVLogicSyntax L
  open CBPVModelSyntax M


  open MonFun renaming (f to fun)
  open BifunctorSepᴰ
  Oᴰ : BifunctorSepᴰ (M .snd .snd) (Vᴰ ^opᴰ) Cᴰ (GRAPHᴰ _ _ _ _ )
  Oᴰ .Bif-obᴰ {A} {B} P Q .fst M = (A LV.◂ P ≤ (pull M $ Q)) , isProp→isSet LV.isProp≤ 
  Oᴰ .Bif-obᴰ {A} {B} P Q .snd {M}{M'} M↦M' P≤MQ P≤M'Q = A LV.◂ pull M $ Q ≤ (pull M' $ Q) , isProp→isSet LV.isProp≤
 -- Oᴰ .Bif-obᴰ {A} {B} P Q .snd = LV.isProp≤
  Oᴰ .Bif-homLᴰ {A} {A'} {V}{P}{P'} P'≤VP {B} Q .fst M P≤MQ = 
    LV.seq  P'≤VP (
    LV.seq (LV.mon* V P≤MQ) (
    LV.eqTo≤ {!  !}))
  Oᴰ .Bif-homLᴰ {A} {A'} {V}{P}{P'} P'≤VP {B} Q .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q MQ≤M'Q = {!   !} where 
    goal : {!   !} 
    goal = {!   !}

  Oᴰ .Bif-L-idᴰ = {!   !}
  Oᴰ .Bif-L-seqᴰ = {!   !}
  Oᴰ .Bif-homRᴰ = {!   !}
  Oᴰ .Bif-R-idᴰ = {!   !}
  Oᴰ .Bif-R-seqᴰ = {!   !}
  Oᴰ .SepBif-RL-commuteᴰ = {!   !}
  
{-}

  Oᴰ .F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .fst M P≤MQ = 
    LV.seq  P'≤VP (
    LV.seq (LV.mon* V P≤MQ)  (
    LV.seq (LV.mon* V (pull M .isMon  Q≤SQ')) (
    LV.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (LSq .N-hom (V , S)) M))))))
  Oᴰ .F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .snd {M}{M'}{M↦M'} P≤MQ P≤M'Q MQ≤M'Q = goal where 
    goal : A' LV.◂ pull (OBif .Bif-hom× V S .fst M) $ Q' ≤ (pull ((OBif .Bif-hom× V S .fst M')) $ Q') 
    goal = {!   !}
  Oᴰ .F-idᴰ = {! pGraphHomᴰ≡ ?  !}
  Oᴰ .F-seqᴰ = {!   !}
-}

  Mᴰ : CBPVModelᴰ M  _ _ _ _ _ _ 
  Mᴰ .fst = Vᴰ
  Mᴰ .snd .fst = Cᴰ
  Mᴰ .snd .snd = Oᴰ

{-




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

  private 
    module VL = HDSyntax VH
    module CL = HDSyntax CH
      
  pull : {A : V .ob}{B : C .ob}(M : O'[ A , B ])  
    → MonFun (F-ob CH B .fst) (F-ob VH A .fst)
  pull {A} {B} M = Sq .N-ob (A , B) M

open Categoryᴰ
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

-}