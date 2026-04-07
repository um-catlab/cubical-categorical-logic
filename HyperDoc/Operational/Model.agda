{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Model where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Operational.TransitionSystemAlt

open Category
open Functor
open TSystem 
record CBPVModel : Type where 
  field 
    V : Category _ _ 
    C : Category _ _ 
    O : Functor ((V ^op) ×C C) TSysCat

  O[_,-] : (v : ob V) → Functor C TSysCat
  O[_,-] v = O ∘F rinj _ _ v

  O[_,_] : ob V → ob C → ob TSysCat
  O[_,_] v c = O .F-ob (v , c)

  O'[_,_] : ob V → ob C → Type 
  O'[_,_] v c = ⟨  O .F-ob (v , c)  .state ⟩ 


record CBPVMorphism (M N : CBPVModel) : Type where
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
  field 
    FV : Functor M.V N.V 
    FC : Functor M.C N.C 
    FO : NatTrans M.O (N.O ∘F ((FV ^opF) ×F FC)) 

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor 
open import Cubical.Categories.Displayed.BinProduct 

record CBPVModelᴰ (M : CBPVModel) : Type where 
  module M = CBPVModel M
  field 
    Vᴰ : Categoryᴰ M.V _ _
    Cᴰ : Categoryᴰ M.C _ _
    Oᴰ : Functorᴰ M.O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) TSysCatᴰ 

open import Cubical.Categories.Instances.Posets.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Functors.HomFunctor
open import HyperDoc.Lib

Hom^op :  Functor ((POSET _ _) ×C (POSET _ _)^op) (SET _)
Hom^op  = (HomFunctor _) ∘F Cubical.Categories.Constructions.BinProduct.Sym
  
{-.F-ob (P , Q) = (POSET _ _) [ Q , P ] , (POSET _ _) .isSetHom
Hom^op .F-hom {(A , B)}{(A' , B')} (f , g) h = MonComp g (MonComp h f)
Hom^op .F-id = funExt λ _ → eqMon _ _ refl
Hom^op .F-seq _ _ = funExt λ _ → eqMon _ _ refl
-}

FORGET : Functor (TSysCat) (SET _) 
FORGET .F-ob S = state  S
FORGET .F-hom f = f .TSystem[_,_].tmap
FORGET .F-id = refl
FORGET .F-seq _ _ = refl

open import HyperDoc.Syntax
open NatTrans

record Logic (M : CBPVModel ) : Type _ where 
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


module ConvertLogic
  (M : CBPVModel)
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
  open import Cubical.Data.Maybe
  open import Cubical.Data.Unit
  open import Cubical.Categories.Displayed.Instances.Sets
  open MonFun renaming (f to fun)

  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) TSysCatᴰ
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .TSystemᴰ.stateᴰ M = A VL.◂ P ≤ (pull M $ Q) , isProp→isSet VL.isProp≤
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .TSystemᴰ.transᴰ M prf with (O[ A , B ] .trans M)  
  ... | nothing = tt
  ... | just M' = goal where
    have : O'[ A , B ] 
    have = M

    have' : A VL.◂ P ≤ (pull M $ Q)
    have' = prf

    goal : A VL.◂ P ≤ (pull M' $ Q)
    goal = {!   !} 
    
  Oᴰ .Functorᴰ.F-homᴰ (Vᴰ , Sᴰ) .TSysᴰ[_][_,_].tmapᴰ = {!   !}
  Oᴰ .Functorᴰ.F-idᴰ = {!   !}
  Oᴰ .Functorᴰ.F-seqᴰ = {!   !}

  {- 
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

  -}