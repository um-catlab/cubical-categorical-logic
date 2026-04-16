{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.TypeStructure where 
  
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category 
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Category
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf hiding (PshIso ; PshHom)
open import Cubical.Categories.Displayed.Base
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
open PshHom

WkRepresentation : (C : Category _ _ ) (P : Presheaf C _) → Type _
WkRepresentation C P =  Σ[ A ∈ C .ob ] (PshHom (C [-, A ]) P × PshHom P (C [-, A ]))

WkRepresentationᴰ : {C : Category _ _}{P : Presheaf C _} → 
  WkRepresentation C P →
  (Cᴰ : Categoryᴰ C _ _ )(Pᴰ : Presheafᴰ P Cᴰ _ ) → Type _ 
WkRepresentationᴰ wkrep Cᴰ Pᴰ = 
  Σ[ Aᴰ ∈ (Cᴰ .ob[_] (wkrep .fst))] PshHomᴰ (wkrep .snd .fst) (Cᴰ [-][-, Aᴰ ]) Pᴰ × PshHomᴰ (wkrep .snd .snd) Pᴰ (Cᴰ [-][-, Aᴰ ])

module TypeStructure (M : CBPVModel _ _ _ _ _ _ )  where 
  open CBPVModelSyntax M

  record HasUTy : Type where 
    field 
      wkrep : (B : ob C) → WkRepresentation V (FORGET ∘F O[-, B ]) 
    
    U : ob C → ob V 
    U B = wkrep B .fst

    force : {B : ob C} → O'[ U B , B ]
    force {B} = wkrep B .snd .fst .N-ob (U B) (V .id)

    thunk : {A : ob V}{B : ob C} → O'[ A , B ] → V [ A , U B ] 
    thunk {A}{B} = wkrep B .snd .snd  .N-ob A 

    field 
      Fβ : {A : ob V}{B : ob C}{M : O'[ A , B ]} →
        Edge[ O .Bif-homL (thunk M) B .fst force , M ] 

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

-- wtf.. typechecking was fine until this.. (specifically inserting FORGETᴰ)
  record HasUTyᴰ (hasUTy : HasUTy) : Type where 
    field 
      weakrepᴰ : {B : ob C}(Bᴰ : Cᴰ .ob[_] B) → 
        WkRepresentationᴰ (hasUTy .wkrep B) Vᴰ (FORGETᴰ ∘Fᴰ O[-][-, Bᴰ ])
    
  


  --HasUTy : Type 
 -- HasUTy = (B : ob C) → 


  -- ] ⟨ O .Bif-ob (R .fst) B .snd {! R .snd .fst  !} {!   !} ⟩
  -- (FORGET ∘F O[-, B ])
  {-

  Representation : Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  Representation =  Σ[ A ∈ C .ob ] PshIso (C [-, A ]) P

  HasUTy : Type 
  HasUTy = (B : ob C) → Representation V (FORGET ∘F O[-, B ])

  record PshIso : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    constructor pshiso
    field
      trans : PshHom P Q
      nIso : isPshIso {P = P}{Q = Q} trans

  {- a PshIso is a PshHom whose underlying functions are iso -}
  module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
    isPshIso : PshHom P Q → Type _
    isPshIso α = ∀ x → isIso (α .N-ob x)


  hasUTy : HasUTy
  hasUTy B .fst = U B
  hasUTy B .snd .trans .N-ob A V = subC V force
  hasUTy B .snd .trans .N-hom A A' V W = sym subDist ∙ sym plugId
  hasUTy B .snd .nIso A .fst = thunk
  hasUTy B .snd .nIso A .snd .fst M = Uβ
  hasUTy B .snd .nIso A .snd .snd V = Uη

  hasFTy : HasFTy 
  hasFTy A .fst = F A
  hasFTy A .snd .trans .N-ob B S = plug S ret
  hasFTy A .snd .trans .N-hom B B' S S' = sym plugDist ∙ cong₂ plug refl (sym subCId)
  hasFTy A .snd .nIso B .fst = bind
  hasFTy A .snd .nIso B .snd .fst M = Fβ
  hasFTy A .snd .nIso B .snd .snd S = Fη
  

  HasV𝟙 : Type 
  HasV𝟙  = (A : ob V) → Σ[ X ∈ ob V ] ((V [ A , X ]) ↔ Unit)
  
  HasUTy : Type
  HasUTy = (A : ob V)(B : ob C) → Σ[ X ∈ ob V ] (O'[ A , B ] ↔ (V [ A , X ]))

  HasFTy : Type 
  HasFTy = (A : ob V)(B : ob C) → Σ[ X ∈ ob C ] (O'[ A , B ] ↔ (C [ X , B ]))
  -}