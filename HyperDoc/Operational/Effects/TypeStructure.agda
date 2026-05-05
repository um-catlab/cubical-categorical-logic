{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Effects.TypeStructure where 
  
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
open import Cubical.Categories.Displayed.Bifunctor

open import HyperDoc.Algebra.Algebra hiding (FORGET)
open import HyperDoc.Operational.Effects.BiAlgebra
-- open import HyperDoc.Operational.Graph
open import HyperDoc.Operational.Effects.Model
open import HyperDoc.Lib

open BiAlg renaming (Node to bNode ; Edge[_,_] to bEdge[_,_])
open BiAlgᴰ renaming (Nodeᴰ to bNodeᴰ ; Edgeᴰ[_][_,_] to bEdgeᴰ[_][_,_])
open BiAlgHom
open BiAlgHomᴰ
open Category
open Functor
open Categoryᴰ
open BifunctorSep
open BifunctorSepᴰ
open import Cubical.Categories.NaturalTransformation
open import Cubical.Foundations.Isomorphism
open PshHom
open Functorᴰ
open NatTrans
open NatTransᴰ

{-
  Unit, Product, and Coproduct are NOT instances of this.. 
  - Unit has no reduction ..?
  - the elimination rule for product is derivable, and so is its reduction edge
  - For coproduct, we could instaniate with the Collage, but we DO NOT want value reductions
-}
record WkRepresentation
  {Sig : Signature}
  (C : Category _ _ ) 
  (P : Functor (C ^op) (BIALG Sig)) : Type where 

  private 
    Node : (c : ob C) → Type 
    Node c = bNode (P .F-ob c)
    
    Edge : {c : ob C} → Node c → Node c → Type 
    Edge {c} n n' = bEdge[_,_] (P .F-ob c) n n'

  field 
    rep : C .ob 
    fwd : NatTrans (C [-, rep ]) (FORGET ∘F P) 
    bkwd : {c : ob C} → Node c → C [ c , rep ]
    wkretract : {c : ob C}(n : Node c) → Edge (fwd .N-ob c (bkwd n)) n

record WkRepresentationᴰ
  {Sig : Signature}
  {C : Category _ _ }
  {P : Functor (C ^op) (BIALG Sig)}
  (wkrep : WkRepresentation C P)
  (Cᴰ : Categoryᴰ C _ _ )
  (Pᴰ : Functorᴰ P (Cᴰ ^opᴰ) (BIALGᴰ {Sig})) : Type where 
  open WkRepresentation wkrep
  
  private 
    Node : (c : ob C) → Type 
    Node c = bNode (P .F-ob c)
    
    Edge : {c : ob C} → Node c → Node c → Type 
    Edge {c} n n' = bEdge[_,_] (P .F-ob c) n n'

    Nodeᴰ : {c : ob C}(cᴰ : Cᴰ .ob[_] c)(n : Node c) → Type 
    Nodeᴰ {c} cᴰ n = bNodeᴰ (Pᴰ .F-obᴰ {c} cᴰ) n

    Edgeᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n n' : Node c}
      (e : Edge n n')→ (Nodeᴰ cᴰ n) → (Nodeᴰ cᴰ n')→ Type 
    Edgeᴰ {c}{cᴰ}{n}{n'} e nᴰ n'ᴰ = bEdgeᴰ[_][_,_] (Pᴰ .F-obᴰ {c} cᴰ) e  nᴰ n'ᴰ

  field 
    repᴰ : Cᴰ .ob[_] rep
    fwdᴰ : NatTransᴰ fwd (Cᴰ [-][-, repᴰ ]) (FORGETᴰ {Sig} ∘Fᴰ Pᴰ)
    bkwdᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n : Node c} → Nodeᴰ cᴰ n → 
      Cᴰ [ bkwd {c} n ][ cᴰ , repᴰ ] 
    wkretractᴰ : {c : ob C}{cᴰ : Cᴰ .ob[_] c}{n : Node c}(nᴰ : Nodeᴰ cᴰ n) → 
      Edgeᴰ (wkretract {c} n) (fwdᴰ .N-obᴰ cᴰ (bkwd n) (bkwdᴰ nᴰ)) nᴰ
    
module TypeStructure {Sig : Signature}(M : CBPVModel Sig)  where 
  open CBPVModelSyntax M
  open WkRepresentation
  open import Cubical.Categories.Functors.Constant
  open import Cubical.Categories.Presheaf.Constructions.BinProduct.Base

  Has𝟙 : Type 
  Has𝟙 = Σ[ 𝟙 ∈ ob V ]  NatTrans ( Constant _ _  (Unit , isSetUnit)) (V [-, 𝟙 ]) 

  record Has+' (A A' : ob V) : Type where
    private 
      conv : Functor C (BIALG Sig) → Functor (C ^op ^op) (SET _)
      conv F = FORGET ∘F F ∘F from^op^op
    field 
      A+A' : ob V 
      match : NatTrans ((conv  O[ A ,-]) ×Psh (conv O[ A' ,-])) (conv O[ A+A' ,-])
      σ₁ : V [ A , A+A' ]
      σ₂ : V [ A' , A+A' ] 
      +β₁ : {B : ob C} → (M : O'[ A , B ]) → (N : O'[ A' , B ]) → 
        Edge[ O .Bif-homL σ₁ B .map ((match .N-ob B (M , N))) , M ]
      +β₂ : {B : ob C} → (M : O'[ A , B ]) → (N : O'[ A' , B ]) →
        Edge[ O .Bif-homL σ₂ B .map (match .N-ob B (M , N)) , N ]

  Has+ : Type 
  Has+ = (A A' : ob V) → Has+' A A' 

  HasUTy : Type 
  HasUTy = (B : ob C) → WkRepresentation V O[-, B ]

  HasFTy : Type 
  HasFTy = (A : ob V) → WkRepresentation (C ^op) (O[ A ,-] ∘F from^op^op) 

  module UTySyntax (hasUTy : HasUTy) where  
    U : ob C → ob V 
    U B = hasUTy B .rep

    force : {A : ob V}{B : ob C} → V [ A , U B ] → O'[ A , B ] 
    force {A}{B} = hasUTy B .fwd .N-ob A

    thunk : {A : ob V}{B : ob C} → O'[ A , B ] → V [ A , U B ]
    thunk {A}{B} = hasUTy B .bkwd {A}

    Uβ : {A : ob V}{B : ob C} → (M : O'[ A , B ]) → Edge[ force (thunk M) , M ]
    Uβ {A}{B} M = hasUTy B .wkretract {A} M 

  module FTySyntax (hasFTy : HasFTy) where 
    F : ob V → ob C 
    F A = hasFTy A .rep 

    ret : {A : ob V}{B : ob C} → C [ F A , B ] → O'[ A , B ]
    ret {A}{B} = hasFTy A .fwd .N-ob B

    bind : {A : ob V}{B : ob C} → O'[ A , B ] → C [ F A , B ]
    bind {A}{B} = hasFTy A .bkwd

    Fβ : {A : ob V}{B : ob C} → (M : O'[ A , B ]) → Edge[ ret (bind M) , M ] 
    Fβ {A}{B} = hasFTy A .wkretract

module TypeStructureᴰ
  {Sig : Signature}
  {M : CBPVModel Sig}
  (Mᴰ : CBPVModelᴰ M ) where  

  open TypeStructure M
  open CBPVModelSyntax M 
  open CBPVModelᴰSyntax Mᴰ
  open WkRepresentation
  open WkRepresentationᴰ
  open import Cubical.Categories.Functors.Constant
  open import Cubical.Categories.Displayed.Presheaf.Constructions.BinProduct.Base 

  Constantᴰ : Functorᴰ (Constant (V ^op) (SET _) (Unit , isSetUnit)) (Vᴰ ^opᴰ) (SETᴰ _ _)
  Constantᴰ .F-obᴰ _ _ = Unit , isSetUnit
  Constantᴰ .F-homᴰ = λ _ x₁ _ → tt
  Constantᴰ .F-idᴰ = refl
  Constantᴰ .F-seqᴰ _ _ = refl

  Has𝟙ᴰ : Has𝟙 → Type 
  Has𝟙ᴰ has𝟙 = Σ[ 𝟙ᴰ ∈ Vᴰ .ob[_] (has𝟙 .fst) ] NatTransᴰ (has𝟙 .snd) Constantᴰ (Vᴰ [-][-, 𝟙ᴰ ])

  record Has+'ᴰ {A A' : ob V}(has+ : Has+' A A') (Aᴰ : Vᴰ .ob[_] A)(A'ᴰ : Vᴰ .ob[_] A') : Type where
    open Has+' has+
    private
      convᴰ : {F : Functor C (BIALG Sig)} → Functorᴰ F (Cᴰ) ((BIALGᴰ {Sig})) → Functorᴰ (FORGET ∘F F ∘F from^op^op) (Cᴰ ^opᴰ ^opᴰ) ((SETᴰ _ _)) 
      convᴰ {F} Fᴰ = FORGETᴰ ∘Fᴰ (Fᴰ ∘Fᴰ from^opᴰ^opᴰ)
    field 
      Aᴰ+A'ᴰ : Vᴰ .ob[_] A+A'
      matchᴰ : NatTransᴰ match (convᴰ O[-][ Aᴰ  ,-] ×ᴰPsh convᴰ O[-][ A'ᴰ ,-]) (convᴰ O[-][ Aᴰ+A'ᴰ ,-]) 
      σ₁ᴰ :  Vᴰ [ σ₁ ][ Aᴰ , Aᴰ+A'ᴰ ] 
      σ₂ᴰ :  Vᴰ [ σ₂ ][ A'ᴰ , Aᴰ+A'ᴰ ] 
      +β₁ᴰ : {B : ob C}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]}{N : O'[ A' , B ]}
        {e : Edge[ O .Bif-homL σ₁ B .map (match .N-ob B (M , N)) , M ]}  → 
        (nᴰ : Nodeᴰ[ M ][ Aᴰ , Bᴰ ])→ 
        (n'ᴰ : Nodeᴰ[ N ][ A'ᴰ , Bᴰ ]) → 
        Edgeᴰ[ e ][  Oᴰ .Bif-homLᴰ σ₁ᴰ Bᴰ .mapᴰ (N-ob match B (M , N)) (matchᴰ .N-obᴰ Bᴰ (M , N) (nᴰ , n'ᴰ)) , nᴰ  ]
      +β₂ᴰ : {B : ob C}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]}{N : O'[ A' , B ]}
        {e : Edge[ O .Bif-homL σ₂ B .map (match .N-ob B (M , N)) , N ]}  → 
        (nᴰ : Nodeᴰ[ M ][ Aᴰ , Bᴰ ])→ 
        (n'ᴰ : Nodeᴰ[ N ][ A'ᴰ , Bᴰ ]) → 
        Edgeᴰ[ e ][  Oᴰ .Bif-homLᴰ σ₂ᴰ Bᴰ .mapᴰ (N-ob match B (M , N)) (matchᴰ .N-obᴰ Bᴰ (M , N) (nᴰ , n'ᴰ)) , n'ᴰ  ]

  Has+ᴰ : Has+ → Type 
  Has+ᴰ has+ = {A A' : ob V}(Aᴰ : Vᴰ .ob[_] A)(A'ᴰ : Vᴰ .ob[_] A') → Has+'ᴰ {A}{A'} (has+ A A') Aᴰ A'ᴰ

  HasUTyᴰ : HasUTy → Type 
  HasUTyᴰ hasUTy = {B : ob C}(Bᴰ : Cᴰ .ob[_] B) → 
    WkRepresentationᴰ {C = V}{O[-, B ]} (hasUTy B) Vᴰ O[-][-, Bᴰ ]

  HasFTyᴰ : HasFTy → Type 
  HasFTyᴰ hasFTy = {A : ob V}(Aᴰ : Vᴰ .ob[_] A) →
    WkRepresentationᴰ {C = C ^op} {O[ A ,-] ∘F from^op^op} 
      (hasFTy A) (Cᴰ ^opᴰ) (O[-][ Aᴰ ,-] ∘Fᴰ from^opᴰ^opᴰ) 
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

  module FTySyntaxᴰ 
    {hasFTy : HasFTy}
    (hasFTyᴰ : HasFTyᴰ hasFTy) where

    open FTySyntax hasFTy 

    Fᴰ : {A : ob V} → Vᴰ .ob[_] A → Cᴰ .ob[_] (F A)
    Fᴰ {A} Aᴰ = hasFTyᴰ Aᴰ .repᴰ

    retᴰ :{A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{S : C [ F A , B ]} → 
       Cᴰ [ S ][ Fᴰ Aᴰ , Bᴰ ] → Oᴰ'[ ret S ][ Aᴰ , Bᴰ ]  
    retᴰ{A}{B}{Aᴰ}{Bᴰ}{f} fᴰ = hasFTyᴰ Aᴰ .fwdᴰ .N-obᴰ {B} Bᴰ f fᴰ

    bindᴰ :{A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]} → 
      Oᴰ'[ M ][ Aᴰ , Bᴰ ] → Cᴰ [ bind M ][ Fᴰ Aᴰ , Bᴰ ]  
    bindᴰ{A}{B}{Aᴰ}{Bᴰ}{M} Mᴰ = hasFTyᴰ Aᴰ .bkwdᴰ {B}{Bᴰ}{M} Mᴰ

    Fβᴰ : {A : ob V}{B : ob C}{Aᴰ : Vᴰ .ob[_] A}{Bᴰ : Cᴰ .ob[_] B}{M : O'[ A , B ]} →  
      (Mᴰ : Oᴰ'[ M ][ Aᴰ , Bᴰ ]) → Edgeᴰ[ Fβ M ][ retᴰ (bindᴰ Mᴰ) , Mᴰ ]
    Fβᴰ {Aᴰ = Aᴰ} = hasFTyᴰ Aᴰ .wkretractᴰ
