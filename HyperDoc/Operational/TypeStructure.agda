{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.TypeStructure where 
  
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf hiding (PshIso ; PshHom)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Presheaf.Morphism
open import Cubical.Categories.Displayed.Presheaf.Base 
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Functor

open import HyperDoc.Operational.Graph
open import HyperDoc.Operational.Model
open import HyperDoc.Lib

open Category
open Categoryᴰ
open BifunctorSep
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism
open PshHom
open Functorᴰ
open NatTrans
open NatTransᴰ

record WkRepresentation
  (C : Category _ _ ) 
  (P : Functor (C ^op) (GRAPH _ _)) : Type where 

  private 
    Node : (c : ob C) → Type 
    Node c = ⟨ Functor.F-ob P c .fst ⟩ 

    Edge : {c : ob C} → Node c → Node c → Type 
    Edge {c} n n' = ⟨ Functor.F-ob P c .snd n n'  ⟩

  field 
    rep : C .ob 
    fwd : NatTrans (C [-, rep ]) (FORGET ∘F P) 
    bkwd : {c : ob C} → Node c → C [ c , rep ]
    wkretract : {c : ob C}(n : Node c) → Edge (fwd .N-ob c (bkwd n)) n


record WkRepresentationᴰ
  {C : Category _ _ }
  {P : Functor (C ^op) (GRAPH _ _)}
  (wkrep : WkRepresentation C P)
  (Cᴰ : Categoryᴰ C _ _ )
  (Pᴰ : Functorᴰ P (Cᴰ ^opᴰ) (GRAPHᴰ _ _ _ _)) : Type where 
  open WkRepresentation wkrep
  
  private 
    Node : (c : ob C) → Type 
    Node c = ⟨ Functor.F-ob P c .fst ⟩ 

    Nodeᴰ : {c : ob C}(cᴰ : Cᴰ .ob[_] c)(n : Node c) → Type 
    Nodeᴰ {c} cᴰ n = ⟨ Pᴰ .F-obᴰ {c} cᴰ .fst n ⟩

    Edge : {c : ob C} → Node c → Node c → Type 
    Edge {c} n n' = ⟨ Functor.F-ob P c .snd n n' ⟩

    Edgeᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n n' : Node c}
      (e : Edge n n')→ (Nodeᴰ cᴰ n) → (Nodeᴰ cᴰ n')→ Type 
    Edgeᴰ {c}{cᴰ}{n}{n'} e nᴰ n'ᴰ = ⟨ Pᴰ .F-obᴰ {c} cᴰ .snd {n}{n'} e nᴰ n'ᴰ ⟩

  field 
    repᴰ : Cᴰ .ob[_] rep
    fwdᴰ : NatTransᴰ fwd (Cᴰ [-][-, repᴰ ]) (FORGETᴰ ∘Fᴰ Pᴰ)
    bkwdᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n : Node c} → Nodeᴰ cᴰ n → 
      Cᴰ [ bkwd {c} n ][ cᴰ , repᴰ ] 
    wkretractᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n : Node c}(nᴰ : Nodeᴰ cᴰ n) → 
      Edgeᴰ (wkretract {c} n) (fwdᴰ .N-obᴰ cᴰ (bkwd n) (bkwdᴰ nᴰ)) nᴰ
    
module TypeStructure (M : CBPVModel _ _ _ _ _ _ )  where 
  open CBPVModelSyntax M
  open WkRepresentation

  HasUTy : Type 
  HasUTy = (B : ob C) → WkRepresentation V O[-, B ]


  module UTySyntax (hasUTy : HasUTy) where  
    U : ob C → ob V 
    U B = hasUTy B .rep

    force : {A : ob V}{B : ob C} → V [ A , U B ] → O'[ A , B ] 
    force {A}{B} = hasUTy B .fwd .N-ob A

    thunk : {A : ob V}{B : ob C} → O'[ A , B ] → V [ A , U B ]
    thunk {A}{B} = hasUTy B .bkwd {A}

    Uβ : {A : ob V}{B : ob C} → (M : O'[ A , B ]) → Edge[ force (thunk M) , M ]
    Uβ {A}{B} M = hasUTy B .wkretract {A} M 

  HasFTy : Type 
  HasFTy = (A : ob V) → WkRepresentation (C ^op) (O[ A ,-] ∘F from^op^op) 

  module FTySyntax (hasFTy : HasFTy) where 
    F : ob V → ob C 
    F A = hasFTy A .rep 

    bind : {A : ob V}{B : ob C} → C [ F A , B ] → O'[ A , B ]
    bind {A}{B} = hasFTy A .fwd .N-ob B

    ret : {A : ob V}{B : ob C} → O'[ A , B ] → C [ F A , B ]
    ret {A}{B} = hasFTy A .bkwd

    Fβ : {A : ob V}{B : ob C} → (M : O'[ A , B ]) → Edge[ bind (ret M) , M ] 
    Fβ {A}{B} = hasFTy A .wkretract

module TypeStructureᴰ
  {M : CBPVModel _ _ _ _ _ _ }-----------
  (Mᴰ : CBPVModelᴰ M _ _ _ _ _ _ ) where  

  open TypeStructure M
  open CBPVModelSyntax M 
  open CBPVModelᴰSyntax Mᴰ
  open WkRepresentation
  open WkRepresentationᴰ


  HasUTyᴰ : HasUTy → Type 
  HasUTyᴰ hasUTy = {B : ob C}(Bᴰ : Cᴰ .ob[_] B) → 
    WkRepresentationᴰ {V}{O[-, B ]} (hasUTy B) Vᴰ O[-][-, Bᴰ ]

  module UTySyntaxᴰ 
    {hasUTy : HasUTy}
    (hasUTyᴰ : HasUTyᴰ hasUTy) where 

    open UTySyntax hasUTy 

    Uᴰ : {B : ob C} → Cᴰ .ob[_] B → Vᴰ .ob[_] (U B)
    Uᴰ {B} Bᴰ = hasUTyᴰ Bᴰ .repᴰ

    forceᴰ :{A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{V' : V [ A , U B ]} → 
       Vᴰ [ V' ][ Aᴰ , Uᴰ Bᴰ ] → Oᴰ'[ force V' ][ Aᴰ , Bᴰ ]  
    forceᴰ{A}{B}{Aᴰ}{Bᴰ}{f} fᴰ = hasUTyᴰ Bᴰ .fwdᴰ .N-obᴰ {A} Aᴰ f fᴰ

    thunkᴰ :{A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]} → 
      Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Vᴰ [ thunk M ][ Aᴰ , Uᴰ Bᴰ ]  
    thunkᴰ{A}{B}{Aᴰ}{Bᴰ}{M} Mᴰ = hasUTyᴰ Bᴰ .bkwdᴰ {A}{Aᴰ}{M} Mᴰ

    Uβᴰ : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]} →  
      (Mᴰ : Oᴰ'[ M ][ Aᴰ , Bᴰ ]) → Edgeᴰ[ Uβ M ][ forceᴰ (thunkᴰ Mᴰ) , Mᴰ ]
    Uβᴰ {Bᴰ = Bᴰ} = hasUTyᴰ Bᴰ .wkretractᴰ

  HasFTyᴰ : HasFTy → Type 
  HasFTyᴰ hasFTy = {A : ob V}(Aᴰ : Vᴰ .ob[_] A) →
    WkRepresentationᴰ {C ^op} {O[ A ,-] ∘F from^op^op} 
      (hasFTy A) (Cᴰ ^opᴰ) (O[-][ Aᴰ ,-] ∘Fᴰ from^opᴰ^opᴰ) 


  module FTySyntaxᴰ 
    {hasFTy : HasFTy}
    (hasFTyᴰ : HasFTyᴰ hasFTy) where

    open FTySyntax hasFTy 

    Fᴰ : {A : ob V} → Vᴰ .ob[_] A → Cᴰ .ob[_] (F A)
    Fᴰ {A} Aᴰ = hasFTyᴰ Aᴰ .repᴰ

    bindᴰ :{A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{S : C [ F A , B ]} → 
       Cᴰ [ S ][ Fᴰ Aᴰ , Bᴰ ] → Oᴰ'[ bind S ][ Aᴰ , Bᴰ ]  
    bindᴰ{A}{B}{Aᴰ}{Bᴰ}{f} fᴰ = hasFTyᴰ Aᴰ .fwdᴰ .N-obᴰ {B} Bᴰ f fᴰ




{-}
WkRepresentationᴰ : {C : Category _ _}{P : Presheaf C _} → 
  WkRepresentation C P →
  (Cᴰ : Categoryᴰ C _ _ )(Pᴰ : Presheafᴰ P Cᴰ _ ) → Type _ 
WkRepresentationᴰ wkrep Cᴰ Pᴰ = 
  Σ[ Aᴰ ∈ (Cᴰ .ob[_] (wkrep .fst))] 
    PshHomᴰ (wkrep .snd .fst) (Cᴰ [-][-, Aᴰ ]) Pᴰ × 
    PshHomᴰ (wkrep .snd .snd) Pᴰ (Cᴰ [-][-, Aᴰ ])

module TypeStructure (M : CBPVModel _ _ _ _ _ _ )  where 
  open CBPVModelSyntax M


  record HasFTy : Type where 
    field 
      wkrep : (A : ob V) → WkRepresentation (C ^op) (FORGET ∘F O[ A ,-] ∘F from^op^op) 
    
    F : ob V → ob C 
    F A = wkrep A .fst

    ret : {A : ob V} → O'[ A , F A ] 
    ret {A} = wkrep A .snd .fst  .N-ob (F A) (C .id)

    bind : {A : ob V}{B : ob C} → O'[ A , B ] → C [ F A , B ] 
    bind {A}{B} = wkrep A .snd .snd .N-ob B

    field 
      FU : {A : ob V}{B : ob C}{M : O'[ A , B ]} →
        Edge[ O .Bif-homR A (bind M) .fst ret , M ] 

module DisplayedTypeStructure 
  {M : CBPVModel _ _ _ _ _ _ }
  {Mᴰ : CBPVModelᴰ M _ _ _ _ _ _ } where  

  open TypeStructure M
  open CBPVModelSyntax M 
  open CBPVModelᴰSyntax Mᴰ
  open HasUTy
-}

-- wtf.. typechecking was fine until this.. (specifically inserting FORGETᴰ)
  {-record HasUTyᴰ (hasUTy : HasUTy) : Type where 
    field 
      weakrepᴰ : {B : ob C}(Bᴰ : Cᴰ .ob[_] B) → 
        WkRepresentationᴰ (hasUTy .wkrep B) Vᴰ (FORGETᴰ ∘Fᴰ O[-][-, Bᴰ ])
    -}
  
