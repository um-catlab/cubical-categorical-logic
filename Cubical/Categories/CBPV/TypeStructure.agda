{-# OPTIONS --type-in-type #-}
module Cubical.Categories.CBPV.TypeStructure where 
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Presheaf.Properties
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct.LocalRepresentability
open import Cubical.Data.Sigma
open EnrichedCategory
open EnrichedFunctor
open Category
open import Cubical.Categories.Presheaf.Representable
open UniversalElement
--private 
 -- variable
 --   ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm : Level

module UType 
  (((ctx , vTy , vTm , _ , lr ) , Stk , cTm) : CBPVModel _ _ _ _ _ _ ) where 
  --ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm) where

  cTy = Stk .ob

  ×c : vTy → Functor ctx ctx 
  ×c A = LRPsh→Functor (vTm A , lr A)

  contvTm : (A A' : vTy) → Presheaf ctx _ -- ℓVTm
  contvTm A A' = reindPsh (×c A) (vTm A')
  
  contcTm : vTy → cTy → Presheaf ctx _
  contcTm A B = reindPsh (×c A) (cTm  .F-ob B)

  hasU : Type _ 
  hasU = Σ[ U ∈ (cTy → vTy) ] ((B : cTy) → 
    PshIso ctx (vTm (U B)) (cTm .F-ob B))

  hasF : Type _ 
  hasF = Σ[ F ∈ (vTy → cTy) ] ((A : vTy)(B : cTy) → 
    PshIso ctx (contcTm A B) (Stk .Hom[_,_] (F A) B))

  open import Cubical.Categories.NaturalTransformation.Base

  module _ 
    ((F , isoF) : hasF)
    ((U , isoU) : hasU) where 

    open import Cubical.Categories.NaturalTransformation.More
    _ = _∘ʳⁱ_

    _ = {!   !} ∘ʳⁱ {! isoF  !}

    -- just compose isos
    adj : (A : vTy)(B : cTy) → 
      PshIso ctx (contvTm A (U B)) (Stk .Hom[_,_] (F A) B) 
    adj A B = {! isoU B   !} where 
      foo : PshIso ctx (contvTm A (U B)) (contcTm A B) 
      foo = {! ×c A  !}  ∘ʳⁱ {! isoU B  !} 
        -- {!   !} A ∘ʳⁱ {! isoF A B  !}

module adj 
  (((ctx , vTy , vTm , _ , lr ) , Stk , CTm) : CBPVModel _ _ _ _ _ _ ) where 
  --ℓC ℓC' ℓVTy ℓVTm ℓCTy ℓCTm) where

  cTy = Stk .ob

  --AdjStructure : Type _ 
  --AdjStructure = (A : vTy)(B : ob Stk) → PshIso ctx (vTm A) (Stk .Hom[_,_] B B)

  ×c : vTy → Functor ctx ctx 
  ×c A = LRPsh→Functor (vTm A , lr A)

  cont : (A A' : vTy) → Presheaf ctx _ -- ℓVTm
  cont A A' = reindPsh (×c A) (vTm A')

  record AdjStructure : Type {!ℓCTm   !} where 
    field 
      F : vTy → cTy 
      U : cTy → vTy
      adj : (A : vTy)(B : cTy) → 
        PshIso ctx (cont A (U B)) (Stk .Hom[_,_] (F A) B)


module example where 
  open import Cubical.Categories.CBPV.Instances.DefinedSubstitution
  open import Cubical.Categories.NaturalTransformation.Base hiding (_⇒_)
  open NatTrans
  open Functor
  open import Cubical.Data.List
  open import Cubical.Data.List.Dependent

  Vtm = CBPVDefSubst .fst .snd .snd .fst
  Ctm = CBPVDefSubst .snd .snd .F-ob

  Ustr : {B : CTy} → NatTrans (Vtm (U B)) (Ctm B) × NatTrans (Ctm B) (Vtm (U B)) 
  Ustr .fst .N-ob Γ = force
  Ustr .fst .N-hom _ = refl
  Ustr .snd .N-ob Γ = thunk
  Ustr .snd .N-hom _ = refl

  _×C- : VTy → Functor SubCat SubCat 
  (A ×C-) .F-ob Γ = A ∷ Γ
  (A ×C-) .F-hom = liftSub
  (A ×C-) .F-id = s⟨ refl ⟩∷⟨ refl ⟩
  (A ×C-) .F-seq = {!   !}

  𝓞[_,_] : VTy → CTy → Presheaf SubCat ℓ-zero  
  𝓞[_,_] A B = reindPsh (A ×C-) (Ctm B)

  𝓒[_,_] : CTy → CTy → Presheaf SubCat ℓ-zero 
  𝓒[_,_] B B' = Ehom B B'

  open import Cubical.Categories.WithFamilies.Simple.Instances.Free.Base

  -- can this be natural in A?
  Fstr : {A : VTy}{B : CTy} → NatTrans 𝓒[ F A , B ] 𝓞[ A , B ] ×  NatTrans 𝓞[ A , B ]  𝓒[ F A , B ] 
  Fstr .fst .N-ob Γ S = plug' (subk (wksub idSub) S) (ret (var vz)) 
  Fstr .fst .N-hom γ = funExt λ S → {! u  !}
  Fstr .snd .N-ob Γ M = x←∙:M varc M
  Fstr .snd .N-hom _ = refl


  ArrStr : {A : VTy}{B : CTy} → NatTrans (Ctm (fun A B)) 𝓞[ A , B ] × NatTrans 𝓞[ A , B ]  (Ctm (fun A B))
  ArrStr .fst .N-ob Γ M = app (subc (wksub idSub) M) (var vz)
  ArrStr .fst .N-hom = {!  rec×  !}
  ArrStr .snd .N-ob Γ = lam
  ArrStr .snd .N-hom _ = refl

  open import Cubical.Categories.Presheaf.Constructions.BinProduct
  open import Cubical.Categories.Presheaf.Constructions.Exponential
  open import Cubical.Categories.Presheaf.Morphism.Alt
  ProdStr : {A A' : VTy}{B : CTy} → 
    NatTrans 𝓞[ prod A A' , B ] (Vtm (prod A A') ⇒PshLarge Ctm B) × 
    NatTrans  (Vtm (prod A A') ⇒PshLarge Ctm B) 𝓞[ prod A A' , B ] 
  ProdStr .fst .N-ob Γ M .PshHom.N-ob Δ (γ , V) = subc γ {!   !}
  ProdStr .fst .N-ob Γ M .PshHom.N-hom = {!   !}
  ProdStr .fst .N-hom = {!   !}
  ProdStr .snd .N-ob Γ = {!   !}
  ProdStr .snd .N-hom = {!   !}
  -- no..
  {-
  ProdStr : {A A' : VTy}{B : CTy} → 
   NatTrans ((Ctm B)) (Vtm (prod A A') ×Psh (reindPsh ((A' ×C-)) (reindPsh ((A ×C-)) (Ctm B)))) × 
   NatTrans (Vtm (prod A A') ×Psh (reindPsh ((A' ×C-)) (reindPsh ((A ×C-)) (Ctm B))))  (Ctm B)

  ProdStr .fst .N-ob Γ M = {!   !} , {!   !}
  ProdStr .fst .N-hom = {!   !}
  ProdStr .snd .N-ob Γ (V , M) = rec× V M
  ProdStr .snd .N-hom _ = refl
  -}
  {-
   -- NatTrans (Ctm B) (𝓞[ prod A A' , B ] ×Psh Vtm (prod A A')) × 
    --NatTrans (𝓞[ prod A A' , B ] ×Psh Vtm (prod A A')) ((Ctm B)) 
  ProdStr .fst .N-ob Γ = {!   !}
  ProdStr .fst .N-hom = {!   !}
  ProdStr .snd .N-ob Γ (M , V) = rec× V {!   !}
  ProdStr .snd .N-hom  = {!   !}
-}
 -- Fstr : {}
  
  -- forget about this ever finishing 
  -- open adj CBPVDefSubst

