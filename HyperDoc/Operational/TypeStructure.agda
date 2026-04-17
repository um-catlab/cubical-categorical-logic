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

-- representation up to beta
-- retraction up to reduction
--  ret : f ⋆⟨ C ⟩ inv ≡ C .id

GraphRetract : {X : hSet _}{G : Graph _ _ } → 
  (⟨ X ⟩ → ⟨ G .fst ⟩) → (⟨ G .fst ⟩ → ⟨ X ⟩ ) → Type _ 
GraphRetract {X}{G} f inv = (n : ⟨ G .fst ⟩) → ⟨ G .snd (f (inv n)) n ⟩ 


hasGraphRetract : {!   !}
hasGraphRetract = {!   !}

record isGraphRetract (C : Category _ _){x y : C .ob}(f : C [ x , y ]) : Type _ where
  constructor isiso
  field
    inv : C [ y , x ]
    ret : f ⋆⟨ C ⟩ inv ≡ C .id

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
      (e : Edge n n')→ (Nodeᴰ cᴰ n) →  (Nodeᴰ cᴰ n')→ Type 
    Edgeᴰ {c}{cᴰ}{n}{n'} e nᴰ n'ᴰ = ⟨ Pᴰ .F-obᴰ {c} cᴰ .snd {n}{n'} e nᴰ n'ᴰ ⟩

  field 
    repᴰ : Cᴰ .ob[_] rep
    fwd : NatTransᴰ fwd (Cᴰ [-][-, repᴰ ]) (FORGETᴰ ∘Fᴰ Pᴰ)
    bkwd : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n : Node c} → Nodeᴰ cᴰ n → 
      Cᴰ [ bkwd {c} n ][ cᴰ , repᴰ ] 
    wkretractᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n n' : Node c} → 
      (e : Edge n n')(nᴰ : Nodeᴰ cᴰ n)(n'ᴰ : Nodeᴰ cᴰ n') → 
      Edgeᴰ e nᴰ n'ᴰ
    

module TypeStructure (M : CBPVModel _ _ _ _ _ _ )  where 
  open CBPVModelSyntax M


  HasUTy : Type 
  HasUTy = (B : ob C) → WkRepresentation V O[-, B ]

  HasFTy : Type 
  HasFTy = (A : ob V) → WkRepresentation (C ^op) (O[ A ,-] ∘F from^op^op) 

module DisplayedTypeStructure 
  {M : CBPVModel _ _ _ _ _ _ }
  {Mᴰ : CBPVModelᴰ M _ _ _ _ _ _ } where  

  open TypeStructure M
  open CBPVModelSyntax M 
  open CBPVModelᴰSyntax Mᴰ

  HasUTyᴰ : HasUTy → Type 
  HasUTyᴰ hasUTy = {B : ob C}(Bᴰ : Cᴰ .ob[_] B) → 
    WkRepresentationᴰ {V}{O[-, B ]} (hasUTy B) Vᴰ O[-][-, Bᴰ ]



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
  
