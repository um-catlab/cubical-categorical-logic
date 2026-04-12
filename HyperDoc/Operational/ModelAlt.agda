{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.ModelAlt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Bifunctor
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

  _↦O_ : ∀{A B} (M M' : O'[ A , B ]) → Type 
  _↦O_ {A}{B} M M' = O .F-ob (A , B) .snd M M'


  lcomp : ∀{v v' c} → V [ v , v' ] → (TSysCat) [ O[ v' , c ] , O[ v , c ] ]
  lcomp f = O .F-hom (f , (C .id))

  rcomp : ∀{v c c'} → C [ c , c' ] → (TSysCat) [ O[ v , c ] , O[ v , c' ] ]
  rcomp g = O .F-hom ((V .id) , g)

  lrcomp : ∀{v v' c c'} → V [ v' , v ] → C [ c , c' ] → (TSysCat) [ O[ v , c ] , O[ v' , c' ] ]
  lrcomp V S = O .F-hom (V , S)

  lcompId : ∀{v c}{M : O'[ v , c ]} → lcomp (V .id) .fst M ≡ M
  lcompId {v}{c}{M} i = O .F-id  i .fst M 
    
  rcompId : ∀{v c}{M : O'[ v , c ]} → rcomp (C .id) .fst M ≡ M
  rcompId {v}{c}{M} i = O .F-id  i .fst M 

  lcompSeq : ∀ {v v' v'' c }{W : V [ v , v' ]}{Y : V [ v' , v'' ]}{M : O'[ v'' , c ]} → 
    lcomp  W .fst (lcomp Y .fst M) ≡ lcomp (W ⋆⟨ V ⟩ Y) .fst M
  lcompSeq {W = W}{Y}{M} = 
    funExt⁻ (cong fst (sym (O .F-seq (Y , C .id) (W , C .id)))) M 
    ∙ cong (λ h → O .F-hom ((V ⋆ W) Y , h ) .fst M ) (C .⋆IdL _)

  rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O'[ v , c ]} → 
    rcomp  S' .fst (rcomp S .fst M) ≡ rcomp (S ⋆⟨ C ⟩ S') .fst M
  rcompSeq {S = S}{S'}{M} = 
    funExt⁻ (cong fst (sym (O .F-seq (V .id , S) (V .id , S')))) M  
    ∙ cong (λ h → O .F-hom (h , (C ⋆ S) S') .fst M) (V .⋆IdL _) 

  lrSeq : ∀ {A A' B B'}{W : V [ A , A' ]}{M : O'[ A' , B ]}{S : C [ B , B' ]} → 
    lcomp W .fst (rcomp S .fst M) ≡ rcomp S .fst (lcomp W .fst M)
  lrSeq {W = W}{M}{S} = 
      funExt⁻ (cong fst (sym (O .F-seq _ _))) M 
      ∙ cong₂ 
          (λ h h' → fst (O .F-hom (h , h')) M) 
          (V .⋆IdR _ ∙ sym (V .⋆IdL _)) 
          (C .⋆IdR _ ∙ sym (C .⋆IdL _)) 
      ∙ funExt⁻ (cong fst (O .F-seq _ _)) M

open import Cubical.Categories.Instances.Sets

SetModel : CBPVModel
SetModel .CBPVModel.V = SET _
SetModel .CBPVModel.C = TSysCat
SetModel .CBPVModel.O .F-ob (X , (S , R)) .fst = ⟨ X ⟩ → S 
SetModel .CBPVModel.O .F-ob (X , (S , R)) .snd f g =  (x : ⟨ X ⟩ ) → R (f x) (g x)
SetModel .CBPVModel.O .F-hom {X , S} {Y , T} (f , g) .fst h y = g .fst (h (f y))
SetModel .CBPVModel.O .F-hom {X , S} {Y , T} (f , g) .snd {h}{h'} hRh' y = g .snd (hRh' (f y))
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
open Functorᴰ
open Categoryᴰ
record CBPVModelᴰ (M : CBPVModel) : Type where 
  module M = CBPVModel M
  field 
    Vᴰ : Categoryᴰ M.V _ _
    Cᴰ : Categoryᴰ M.C _ _
    Oᴰ : Functorᴰ M.O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) TSysCatᴰ

  Oᴰ[_,_] : {A : ob M.V}{B : ob M.C}→  Vᴰ .ob[_] A → Cᴰ .ob[_] B → ob[ TSysCatᴰ ] M.O[ A , B ]
  Oᴰ[_,_] Aᴰ Bᴰ = Oᴰ .F-obᴰ (Aᴰ , Bᴰ ) 

  Oᴰ'[_][_,_] : {A : ob M.V}{B : ob M.C}→ M.O'[ A , B ] →  Vᴰ .ob[_] A → Cᴰ .ob[_] B → Type
  Oᴰ'[_][_,_] M Aᴰ Bᴰ = Oᴰ .F-obᴰ (Aᴰ , Bᴰ ) .fst M

  OᴰBif : Bifunctorᴰ (ParFunctorToBifunctor M.O) (Vᴰ ^opᴰ) Cᴰ TSysCatᴰ
  OᴰBif = ParFunctorᴰToBifunctorᴰ Oᴰ

  OᴰRel[_][_,_] : {A : ob M.V}{Aᴰ : Vᴰ .ob[_] A}{B : ob M.C}{Bᴰ : Cᴰ .ob[_] B}{M M' : M.O'[ A , B ]} → M._↦O_ M M'  →  Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Oᴰ'[ M' ][ Aᴰ , Bᴰ ] → Type
  OᴰRel[_][_,_] {A}{Aᴰ}{B}{Bᴰ}{M}{M'} MRM' P Q  = Oᴰ .F-obᴰ (Aᴰ , Bᴰ )  .snd  MRM' P Q

  lcompᴰ : ∀ {A A' B aᴰ a'ᴰ bᴰ}{f : M.V [ A , A' ]} → (fᴰ : Hom[ Vᴰ ][ f , aᴰ ] a'ᴰ) →  Hom[ TSysCatᴰ ][ M.lcomp f , Oᴰ[ a'ᴰ , bᴰ ] ] Oᴰ[ aᴰ , bᴰ ] 
  lcompᴰ {f = f} fᴰ = Oᴰ .F-homᴰ {f = (f , M.C .id)} (fᴰ , Cᴰ .idᴰ)
  {-
    lcompᴰ : ∀ {A A' B aᴰ a'ᴰ bᴰ}{f : V [ A , A' ]} → (fᵈ : Hom[ Vᴰ ][ f , aᴰ ] a'ᴰ) →  Hom[ (ALGᴰ {Σ}) ][ lcomp f , Oᴰ[ a'ᴰ , bᴰ ] ] Oᴰ[ aᴰ , bᴰ ]
  lcompᴰ {f = f} fᴰ = Oᴰ .F-homᴰ {f = (f , C .id)} (fᴰ , Cᴰ .idᴰ)

  rcompᴰ : ∀ {A B B' aᴰ bᴰ b'ᴰ}{f : C [ B , B' ]} → (fᵈ : Hom[ Cᴰ ][ f , bᴰ ] b'ᴰ) →  Hom[ (ALGᴰ {Σ}) ][ rcomp f , Oᴰ[ aᴰ , bᴰ ] ] Oᴰ[ aᴰ , b'ᴰ ]
  rcompᴰ {f = f} fᴰ = Oᴰ .F-homᴰ {f = (V .id , f)} (Vᴰ .idᴰ , fᴰ)


    Oᴰ[_,_] : {A : ob V}{B : ob C} → (aᴰ : ob[ Vᴰ ] A) → (bᴰ : ob[ Cᴰ ] B) →  ob[ (ALGᴰ {Σ}) ] (O .F-ob (A  , B)) 
  Oᴰ[_,_] {A}{B} aᴰ bᴰ  = Oᴰ .F-obᴰ {(A , B)} (aᴰ , bᴰ)
    -}

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
  
  field 
    antiRed : {A : V .ob}{B : C .ob}{Q : CL.F∣ B ∣}{M M' : O'[ A , B ]} → 
      M ↦O M' → 
      ----------------------------------
      A VL.◂ pull M' $ Q ≤ (pull M $ Q) 


  pullComp : ∀ {A A' B B'}(V : V [ A' , A ])(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (lrcomp V S .fst M) ≡ MonComp (CH .F-hom S) (MonComp (pull M) (VH .F-hom V))
  pullComp V S M = funExt⁻ (Sq .N-hom (V , S)) M

  pullLComp : ∀ {A A' B}(V : V [ A' , A ])(M : O'[ A , B ]) → 
    pull (lcomp V .fst M) ≡ MonComp (pull M) (VH .F-hom V)
  pullLComp V M = pullComp V (C .id) M  ∙ cong (λ h → MonComp h (MonComp (pull M) (VH .F-hom V))) (CH .F-id)

  pullRComp :  ∀ {A B B'}(S : C [ B , B' ])(M : O'[ A , B ]) → 
    pull (rcomp S .fst M) ≡ MonComp (CH .F-hom S) (pull M)
  pullRComp S M = pullComp (V .id) S M ∙ cong₂ MonComp refl (VH .F-id)

  V*M*→VM* : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : CL.F∣ B ∣}  → A VL.◂ VL.f* V (pull M $ Q) ≤ (pull (lcomp V .fst M) $ Q) 
  V*M*→VM* = VL.eqTo≤ (cong₂ MonFun.f (sym (pullLComp _ _ )) refl)

  VM*→V*M*  : ∀ {A A' B}{V : V [ A , A' ]}{M : O'[ A' , B ]}{Q : CL.F∣ B ∣} →  A VL.◂ (pull (lcomp V .fst M) $ Q) ≤ VL.f* V (pull M $ Q)
  VM*→V*M* = VL.eqTo≤ (cong₂ MonFun.f (pullLComp _ _ ) refl)

open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
open import Cubical.Categories.Instances.Preorders.Monotone
module Push
  {M : CBPVModel}
  (L : Logic M) where 

  open CBPVModel M 
  open Logic L

  private 
    module VL = HDSyntax VH 
    module CL = HDSyntax CH 

  HasPush : Type
  HasPush = 
    ∀ {A : V .ob}
      {B : C .ob} → 
      (M : O'[ A , B ]) → 
      HasLeftAdj (pull M)

  module PushSyntax (pp : HasPush) where 
    open import Cubical.Foundations.Isomorphism
    open Iso
    open _⊣_ 
    pushToPull : 
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q  → 
      A VL.◂ P ≤ pull M .MonFun.f Q
    pushToPull M  = adjIff (pp M .snd) .fun 

    pullToPush : 
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {P : VL.F∣ A ∣}
      {Q : CL.F∣ B ∣}→ 
      A VL.◂ P ≤ pull M .MonFun.f Q → 
      B CL.◂ pp M .fst .MonFun.f P ≤ Q 
    pullToPush M  = adjIff (pp M .snd) .inv 

    pullPush :       
      ∀ {A : V .ob}
      {B : C .ob}
      (M : O'[ A , B ])
      {Q : CL.F∣ B ∣}
      → A VL.◂ pull M .MonFun.f Q ≤ pull M .MonFun.f Q
    pullPush M = pushToPull M (pullToPush M VL.id⊢)
      

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
  

  open import Cubical.Data.Sigma
  
  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) TSysCatᴰ
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .fst M = A VL.◂ P ≤ (pull M $ Q)
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .snd {M}{M'} M↦M' P≤M*Q P≤M'*Q = A VL.◂ pull M' $ Q ≤ (pull M $ Q)
    {- exactly the same goal -} 
     --A VL.◂ P ≤ (pull M' $ Q) → 
     ------------------------
     --A VL.◂ P ≤ (pull M $ Q)

  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .fst M P≤MQ = 
    VL.seq  P'≤VP (
    VL.seq (VL.mon* V P≤MQ)  (
    VL.seq (VL.mon* V (pull M .isMon  Q≤SQ')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (V , S)) M))))))
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .snd {M}{M'} P≤MQ P≤M'Q M'Q≤MQ = goal where 
    goal : A' VL.◂ pull (O .F-hom (V , S) .fst M') $ Q' ≤ (pull (O .F-hom (V , S) .fst M) $ Q') 
    goal = {!   !}


  {- tran P'≤VM'SQ' = {!   !} where 
    have : A VL.◂ P ≤ (pull M $ Q) 
    have = P≤MQ -- OR ... tran P≤M'Q 

    goal : A' VL.◂ P' ≤ (pull (O .F-hom (V , S) .fst M) $ Q') 
    goal = VL.seq P'≤VM'SQ' {!   !}
-}
  -- M'Q≤MQ = 
    -- prove 
    -- A' | (VM'S)*Q' ⊢ (VMS)*Q'
    -- (VL.mon* V M'Q≤MQ)
  Oᴰ .Functorᴰ.F-idᴰ {A , B} {P , Q}= {! TSHomᴰProp≡ ? (VL.isProp≤ )  !}
    -- toPathP (ΣPathP ((funExt λ x₁ → funExt λ x₂ → VL.isProp≤ _ _) , {!   !}))
  Oᴰ .Functorᴰ.F-seqᴰ = {!   !}


{-
-- no, don't bake in antireduction
  Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) antiTSysCatᴰ
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .fst M = A VL.◂ P ≤ (pull M $ Q)
  Oᴰ .Functorᴰ.F-obᴰ {A , B} (P , Q) .snd {M} {M'} M↦M' P≤M'*Q = VL.seq P≤M'*Q (antiRed M↦M')
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .fst M P≤MQ = 
    VL.seq  P'≤VP (
    VL.seq (VL.mon* V P≤MQ)  (
    VL.seq (VL.mon* V (pull M .isMon  Q≤SQ')) (
    VL.eqTo≤ (sym (cong(λ h → h .fun Q') (funExt⁻ (Sq .N-hom (V , S)) M))))))
  Oᴰ .Functorᴰ.F-homᴰ {A , B} {A' , B'} {V , S} {P , Q} {P' , Q'} (P'≤VP , Q≤SQ') .snd _ _ = VL.isProp≤ _ _
  Oᴰ .Functorᴰ.F-idᴰ = toPathP (antiTSHomᴰ≡ (funExt λ x₁ → funExt λ x₂ → VL.isProp≤ _ _))
  Oᴰ .Functorᴰ.F-seqᴰ _ _ =  toPathP (antiTSHomᴰ≡ (funExt λ x₁ → funExt λ x₂ → VL.isProp≤ _ _))
  -}