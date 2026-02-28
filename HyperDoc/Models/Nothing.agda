{-# OPTIONS --type-in-type #-}
module HyperDoc.Models.Nothing where 



open import Cubical.Data.List 

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Graph.Base 

open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib
open import HyperDoc.CBPVModel
open import HyperDoc.CBPVLogic

open Category
open Functor 

record Raw (ℓV ℓV' ℓC ℓC' ℓS : Level) : Type (levels (ℓsuc (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) where 
  field 
    VG : Graph ℓV ℓV' 
    CG : Graph ℓC ℓC' 
    OF : VG .Node → CG .Node → Type ℓS

module Syntax
  {ℓV ℓV' ℓC ℓC' ℓS : Level }
  (R : Raw ℓV ℓV' ℓC ℓC' ℓS) where

  open Raw R 

  VTy = VG .Node
  CTy = CG .Node


  data _⊢v_ : (A A' : VTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  data _⊢c_ : (A : VTy)(B : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  data _⊢k_ : (B B' : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))

  hole' : ∀ {B} → B ⊢k B
  kcomp' : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''

  data _⊢v_   where
    -- include generators
    incVal : ∀{A A'} → VG .Edge A A' → A ⊢v A'

    -- category 
    subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
    var : ∀ {A} → A ⊢v A
    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)


    isSet⊢v : ∀{A A'} → isSet (A ⊢v A')


  data _⊢c_ where 
    incOb : ∀{A B} → OF A B →  A ⊢c B
    
    subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B -- lcomp
    plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B' -- rcomp

    plugId : ∀ {A B}{M : A ⊢c B} → plug (hole' {B}) M ≡ M
    subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M

    plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
      plug S' (plug S M) ≡ plug (kcomp' S S') M
    subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
      subC V (subC V' M) ≡ subC (subV V V') M
    plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → --both
      subC V (plug S M) ≡ plug S (subC V M)

    isSet⊢c : ∀{A B} → isSet (A ⊢c B)



  data _⊢k_ where 
    incComp : ∀{B B'} → CG .Edge B B' → B ⊢k B'

    -- category 
    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    hole : ∀ {B} → B ⊢k B
    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)

    isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

  hole' = hole
  kcomp' = kcomp


module Initiality where 

  asGraph : ∀{ℓ ℓ'} → Category ℓ ℓ' → Graph ℓ ℓ' 
  asGraph C = record { Node = C .ob ; Edge = C .Hom[_,_] }

  record ModelInterpretation
    {ℓVS ℓV'S ℓCS ℓC'S ℓSS ℓVT ℓV'T ℓCT ℓC'T ℓST : Level}
    (R : Raw ℓVS ℓV'S ℓCS ℓC'S ℓSS)
    (M : Model ℓVT ℓV'T ℓCT ℓC'T ℓST )
    : Type (levels (ℓsuc (ℓVS ∷ ℓV'S ∷ ℓCS ∷ ℓC'S ∷ ℓSS ∷ ℓVT ∷ ℓV'T ∷ ℓCT ∷ ℓC'T ∷ ℓST ∷ []))) where
    open Raw R
    
    open Syntax R
    open GraphHom
    private
      module M = Model M
    field 
      interpV : GraphHom VG (asGraph M.V)
      interpC : GraphHom CG (asGraph M.C)
      interpO : ∀ (A : VG .Node)(B : CG .Node) → A ⊢c B → ⟨ M.O .F-ob ((interpV $g A) , (interpC $g B) ) ⟩ 


module FreeModel 
  {ℓV ℓV' ℓC ℓC' ℓS : Level }
  (R : Raw ℓV ℓV' ℓC ℓC' ℓS) where 

  open Syntax R

  V : Category ℓV (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS)
  V .ob = VTy
  V .Hom[_,_] = _⊢v_
  V .id = var
  V ._⋆_ = subV
  V .⋆IdL = subVIdl
  V .⋆IdR = subVIdr
  V .⋆Assoc = subVAssoc
  V .isSetHom = isSet⊢v

  C : Category ℓC (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) 
  C .ob = CTy
  C .Hom[_,_] = _⊢k_
  C .id = hole
  C ._⋆_ = kcomp
  C .⋆IdL = kcompIdl
  C .⋆IdR = kcompIdr
  C .⋆Assoc = kcompAssoc
  C .isSetHom = isSet⊢k

  O : Functor (V ^op ×C C) (SET (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))) 
  O .F-ob (A , B) = (A ⊢c B) , isSet⊢c
  O .F-hom (V , S) M = subC V (plug S M)
  O .F-id = funExt λ M → cong (λ h → subC var h) plugId ∙ subCId
  O .F-seq (V , S) (V' , S') = 
    funExt λ M → 
      sym subDist 
      ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙ plugSub)

  M : Model  ℓV (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) ℓC (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS) (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓV ℓV') ℓC) ℓC') ℓS)
  M .Model.V = V
  M .Model.C = C
  M .Model.O = O



  module _ (L : Logic{{!   !}}{{!   !}} M) where 
    open import  Cubical.Categories.Constructions.TotalCategory
    open import HyperDoc.AsDisplayed
    open import Cubical.Categories.Displayed.Functor
    open import Cubical.Categories.Displayed.Base
    open import Cubical.Categories.Displayed.BinProduct
    open import Cubical.Data.Sigma
    open import Cubical.Categories.Displayed.Instances.Sets.Base

    convert : Functor ((∫C (Vᴰ M L) ^op) ×C ∫C (Cᴰ M L)) (∫C (((Vᴰ M L) ^opᴰ) ×Cᴰ Cᴰ M L))
    convert .F-ob = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
    convert .F-hom = λ z → (z .fst .fst , z .snd .fst) , z .fst .snd , z .snd .snd
    convert .F-id = refl
    convert .F-seq _ _ = refl

    open import Cubical.Categories.Displayed.Section.Base hiding (GlobalSection)
    module _ (G : Category ℓ-zero ℓ-zero )(F : Functor G ((Model.V M)) ) where 
      open Section
      
     --  module VL = HDSyntax VH 

      test : Section F (Vᴰ M L)
      test .F-obᴰ = {!   !}
      test .F-homᴰ = {!   !}
      test .F-idᴰ {d} = toPathP (VL.isProp≤ M L _ _)
      test .F-seqᴰ _ _ = toPathP (VL.isProp≤ M L _ _)
    

    Total : Model {! Oᴰ  !} {! ΣF  !} {!   !} {!   !} {!   !} 
    Total .Model.V = ∫C (Vᴰ M L)
    Total .Model.C = ∫C (Cᴰ M L)
    Total .Model.O = ΣF ∘F ∫F (Oᴰ M L) ∘F convert

    open ModelMorphism

    -- for free given interpretation
    GlobalSection : ModelMorphism _ _ _ _ _ _ _ _ _ _ M Total 
    GlobalSection .FV .F-ob  n = n , {!   !}
    GlobalSection .FV .F-hom = {!   !}
    GlobalSection .FV .F-id = {!   !}
    GlobalSection .FV .F-seq = {!   !}
    GlobalSection .FC = {!   !}
    GlobalSection .FO = {!   !}