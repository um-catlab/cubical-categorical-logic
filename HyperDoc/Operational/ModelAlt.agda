{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.ModelAlt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Operational.TransitionSystemAltAlt

open Category
open Functor
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
  O'[_,_] v c = O .F-ob (v , c) .fst

open import Cubical.Categories.Instances.Sets

SetModel : CBPVModel
SetModel .CBPVModel.V = SET _
SetModel .CBPVModel.C = TSysCat
SetModel .CBPVModel.O .F-ob (X , (S , R)) .fst = ⟨ X ⟩ → S 
SetModel .CBPVModel.O .F-ob (X , (S , R)) .snd P Q =  (x : ⟨ X ⟩ ) → R (P x) (Q x)
SetModel .CBPVModel.O .F-hom (f , g) .fst h z = g .fst (h (f z))
SetModel .CBPVModel.O .F-hom (f , g) .snd h z = g .snd (h (f z))
SetModel .CBPVModel.O .F-id = refl
SetModel .CBPVModel.O .F-seq _ _ = refl


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
    Oᴰ : Functorᴰ M.O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) {!   !}

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
FORGET .F-ob S = (S .fst) , {!   !}
FORGET .F-hom f x = f .fst x
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
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .fst M = A VL.◂ P ≤ (pull M $ Q)
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .snd {M}{M'} M↦M' P≤M*Q P≤M'*Q = A VL.◂ pull M' $ Q ≤ (pull M $ Q)
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .fst M P≤MQ = 
    VL.seq  P'≤VP (
    VL.seq (VL.mon* V P≤MQ)  (
    VL.seq (VL.mon* V (pull M .isMon  Q≤SQ')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (V , S)) M))))))
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .snd {M}{M'} P≤MQ P≤M'Q M'Q≤MQ = 
    {!   !}
  Oᴰ .Functorᴰ.F-idᴰ = {!   !}
  Oᴰ .Functorᴰ.F-seqᴰ = {!   !}

