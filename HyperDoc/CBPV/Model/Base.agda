{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.CBPV.Model.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.BinProduct 
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation


open import HyperDoc.Algebra.Algebra

open Alg
open AlgHom
open Category
open Functor
open NatTrans

record CBPVModel (Σ : Signature) : Type where 
  field 
    V : Category _ _ 
    C : Category _ _ 
    O : Functor ((V ^op) ×C C) (ALG Σ) 

  O[_,-] : (v : ob V) → Functor C (ALG Σ) 
  O[_,-] v = O ∘F rinj _ _ v

  O[-,_] : (c : ob C) → Functor (V ^op) (ALG Σ) 
  O[-,_] c = O ∘F linj _ _ c

  O[_,_] : ob V → ob C → ob (ALG Σ) 
  O[_,_] v c = O .F-ob (v , c)

  O'[_,_] : ob V → ob C → Type 
  O'[_,_] v c = ⟨ O .F-ob (v , c) .Carrier ⟩ 

  lcomp : ∀{v v' c} → V [ v , v' ] → (ALG Σ) [ O[ v' , c ] , O[ v , c ] ]
  lcomp f = O .F-hom (f , (C .id))

  rcomp : ∀{v c c'} → C [ c , c' ] → (ALG Σ) [ O[ v , c ] , O[ v , c' ] ]
  rcomp g = O .F-hom ((V .id) , g)

  lrcomp : ∀{v v' c c'} → V [ v' , v ] → C [ c , c' ] → (ALG Σ) [ O[ v , c ] , O[ v' , c' ] ]
  lrcomp V S = O .F-hom (V , S)

  lcompId : ∀{v c}{M : O'[ v , c ]} → lcomp (V .id) .carmap M ≡ M
  lcompId {v}{c}{M} i = O .F-id  i .carmap M 
    
  rcompId : ∀{v c}{M : O'[ v , c ]} → rcomp (C .id) .carmap M ≡ M
  rcompId {v}{c}{M} i = O .F-id  i .carmap M 
{-
  
  rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O'[ v , c ]} → 
    rcomp  S' .carmap (rcomp S .carmap M) ≡ rcomp (S ⋆⟨ C ⟩ S') .carmap M
  rcompSeq {S = S}{S'}{M} = {!   !} ∙ {! O .F-seq (V .id , (C ⋆ S) S')  !}
  --cong (λ h → h .carmap M ) {! cong₂ (O .F-hom) (cong₂ _,_ (V .⋆IdL _) refl)  !}
  

rcompSeq : ∀ {v c c' c''}{S : C [ c , c' ]}{S' : C [ c' , c'' ]}{M : O[ v , c ]} → 
  rcomp  S' (rcomp S M) ≡ rcomp (S ⋆⟨ C ⟩ S') M
rcompSeq {S = S}{S'}{M} =  funExt⁻ (sym (O .F-seq (V .id , S) (V .id , S'))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ (V .⋆IdL _) refl) refl

lcompSeq : ∀ {v v' v'' c }{W : V [ v , v' ]}{Y : V [ v' , v'' ]}{M : O[ v'' , c ]} → 
  lcomp  W (lcomp Y M) ≡ lcomp (W ⋆⟨ V ⟩ Y) M
lcompSeq {W = W}{Y}{M}= funExt⁻ (sym (O .F-seq (Y , C .id) (W , C .id))) M ∙ cong₂ (O .F-hom) (cong₂ _,_ refl (C .⋆IdL _)) refl

lrSeq : ∀ {A A' B B'}{W : V [ A , A' ]}{M : O[ A' , B ]}{S : C [ B , B' ]} → 
  lcomp W (rcomp S M) ≡ rcomp S (lcomp W M)
lrSeq {W = W}{M}{S} = 
  funExt⁻ (sym (O .F-seq _ _)) M  
  ∙ cong₂ (O .F-hom ) (cong₂ _,_ (V .⋆IdR _ ∙ sym (V .⋆IdL _)) (C .⋆IdR _ ∙ sym (C .⋆IdL _))) refl 
  ∙ funExt⁻ (O .F-seq _ _ ) M
  -}



record CBPVMorphism {Σ : Signature} (M N : CBPVModel Σ) : Type where
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
  field 
    FV : Functor M.V N.V 
    FC : Functor M.C N.C 
    FO : NatTrans M.O (N.O ∘F ((FV ^opF) ×F FC)) 

idCBPVMorphism : {Σ : Signature} {M : CBPVModel Σ} → CBPVMorphism M M 
idCBPVMorphism .CBPVMorphism.FV = Id
idCBPVMorphism .CBPVMorphism.FC = Id
idCBPVMorphism .CBPVMorphism.FO .N-ob x = idHom
idCBPVMorphism .CBPVMorphism.FO .N-hom f = AlgHom≡ refl



record CBPVModelᴰ {Σ : Signature}(M : CBPVModel Σ) : Type where 
  open CBPVModel M
  field 
    Vᴰ : Categoryᴰ V _ _ 
    Cᴰ : Categoryᴰ C _ _ 
    Oᴰ : Functorᴰ O ((Vᴰ ^opᴰ) ×Cᴰ Cᴰ) (ALGᴰ {Σ})