{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Initial where

open import Cubical.Data.Maybe

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor


open Category
open Functor

mutual 
  data VTy : Type where 
    𝟙 Ans : VTy
    U : CTy → VTy 

  data CTy : Type where 
    F : VTy → CTy

data _⊢v_ : (A A' : VTy) → Type 
data _⊢c_ : (A : VTy)(B : CTy) → Type 
data _⊢k_ : (B B' : CTy) → Type 

subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

data _⊢v_  where
  -- category 
  subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
  var : ∀ {A} → A ⊢v A
  subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
  subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
  subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
    subV (subV V W) Y ≡ subV V (subV W Y)
  isSet⊢v : ∀{A A'} → isSet (A ⊢v A')

  -- type structure
  tt : ∀{A} → A ⊢v 𝟙
  yes : ∀{A} → A ⊢v Ans 
  no : ∀{A} → A ⊢v Ans 
  thunk : ∀{A B} → A ⊢c B → A ⊢v U B


data _⊢k_ where
  -- category 
  kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
  hole : ∀ {B} → B ⊢k B
  kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
  kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
  kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
    kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
  isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

  bind : {A : VTy}{B : CTy} → A ⊢c B → F A ⊢k B

data _⊢c_ where 
  -- profunctor      
  subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
  plugId : ∀ {A B}{M : A ⊢c B} → plug (hole {B}) M ≡ M
  subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
  plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
    plug S' (plug S M) ≡ plug (kcomp S S') M
  subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
    subC V (subC V' M) ≡ subC (subV V V') M
  plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
    subC V (plug S M) ≡ plug S (subC V M)
  isSet⊢c : ∀{A B} → isSet (A ⊢c B)

  -- type structure
  ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
  force : ∀{A B} →  A ⊢v U B → A ⊢c B   

subC' = subC

import  Cubical.Data.Equality as Eq

data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
  Fβ : ∀{A A' B}{V : A ⊢v A'}{M : A' ⊢c B} → 
    ------------------------------------
    plug (bind M) (ret V) ↦ (subC V M)

  Uβ : ∀ {A B} {M : A ⊢c B} → 
    ---------------------
    force (thunk M) ↦ M
  
  subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    subC V M  ↦ subC V M'

  plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    plug S M ↦ plug S M'

  isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')


V : Category ℓ-zero ℓ-zero
V .ob = VTy
V .Hom[_,_] = _⊢v_
V .id = var
V ._⋆_ = subV
V .⋆IdL = subVIdl
V .⋆IdR = subVIdr
V .⋆Assoc = subVAssoc
V .isSetHom = isSet⊢v

C : Category ℓ-zero ℓ-zero 
C .ob = CTy
C .Hom[_,_] = _⊢k_
C .id = hole
C ._⋆_ = kcomp
C .⋆IdL = kcompIdl
C .⋆IdR = kcompIdr
C .⋆Assoc = kcompAssoc
C .isSetHom = isSet⊢k

open import HyperDoc.Operational.TransitionSystemAltAlt 

TSys : VTy → CTy → ob TSysCat
TSys A B .fst = A ⊢c B
TSys A B .snd = _↦_ {A}{B}

open import Cubical.Data.Sigma 
O :  Functor ((V ^op) ×C C) TSysCat
O .F-ob (A , B) = TSys A B
O .F-hom (V , S) .fst M = subC V (plug S M)
O .F-hom (V , S) .snd {M}{M'} M↦M' = subC-cong (plug-cong M↦M')
O .F-id = Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦) 
  (funExt λ M → subCId ∙ plugId)
O .F-seq (V , S)(V' , S') = 
  Σ≡Prop (λ f → isPropImplicitΠ  λ M → isPropImplicitΠ  λ M' → isProp→ isProp↦)  
    (funExt (λ M → sym (subDist )  ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙  plugSub)))


open import HyperDoc.Operational.ModelAlt
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open NatTrans 

Syn : CBPVModel
Syn .CBPVModel.V = V
Syn .CBPVModel.C = C
Syn .CBPVModel.O = O

open CBPVModel using (O[_,-])


CL : CBPVMorphism Syn SetModel 
CL .CBPVMorphism.FV = V [ 𝟙 ,-]
CL .CBPVMorphism.FC = O[_,-] Syn 𝟙
CL .CBPVMorphism.FO .N-ob (A , B) .fst M V = subC V M
CL .CBPVMorphism.FO .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M' 
CL .CBPVMorphism.FO .N-hom {A , B}{A' , B'} (V , S) = 
  ΣPathP ((funExt λ M → funExt λ V' → (subDist ∙ plugSub) ∙ sym subCId) ,
     toPathP (implicitFunExt λ {N} → implicitFunExt λ {N'} → funExt λ N↦N' → funExt λ V' → isProp↦ _ _))


open import HyperDoc.Syntax
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor 
open Functorᴰ

idCBPVMorphism : {M : CBPVModel} → CBPVMorphism M M 
idCBPVMorphism {M} .CBPVMorphism.FV = Id
idCBPVMorphism {M} .CBPVMorphism.FC = Id
idCBPVMorphism {M} .CBPVMorphism.FO .N-ob = λ x → (λ z → z) , (λ {a} {a'} z → z)
idCBPVMorphism {M} .CBPVMorphism.FO .N-hom _ = refl

module ModelSection 
  {M N : CBPVModel }
  (F : CBPVMorphism M N)
  (L : Logic N) where 

  open CBPVMorphism F
  private 
    module M = CBPVModel M 
    module N = CBPVModel N
    module L = Logic L
    module VH' = HDSyntax (L.VH ∘F (FV ^opF))
    module CH' = HDSyntax (L.CH ∘F (FC ^opF))

  open ConvertLogic N L
  module _ 
    (SV : Section FV Vᴰ) 
    (SC : Section FC Cᴰ) where 

    private 
      module SV = Section SV 
      module SC = Section SC
    
    SectionO : Type 
    SectionO = 
      ∀ 
        {A : ob M.V}
        {B : ob M.C}
        (M : M.O[ A , B ] .fst) → 
        Oᴰ .F-obᴰ {FV .F-ob A , FC .F-ob B} (SV.F-obᴰ A , SC.F-obᴰ B)  .fst (FO .N-ob (A , B) .fst M)
      
  CBPVSection : Type 
  CBPVSection = Σ[ SV ∈ Section FV Vᴰ ] Σ[ SC ∈ Section FC Cᴰ ] SectionO SV SC

CBPVGlobalSection : {M : CBPVModel } → Logic M → Type 
CBPVGlobalSection L = ModelSection.CBPVSection idCBPVMorphism L
open import Cubical.Categories.Instances.Preorders.Monotone

open MonFun
module hrm (L : Logic Syn) where 
  open Logic L
  module LV = HDSyntax VH
  module LC = HDSyntax CH

  mutual 
    vty : (A : VTy) → LV.F∣ A ∣ 
    vty 𝟙 = {!   !}
    vty Ans = {!   !}
    vty (U B) = pull (force var) $ cty B

    cty : (B : CTy) → LC.F∣ B ∣
    cty = {!   !} 

    vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
    vtm = {!   !}

    ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
    ktm S = {!   !}

    ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
    ctm (subC x M) = {!   !}
    ctm (plug x M) = {!   !}
    ctm (plugId i) = {!   !}
    ctm (subCId i) = {!   !}
    ctm (plugDist i) = {!   !}
    ctm (subDist i) = {!   !}
    ctm (plugSub i) = {!   !}
    ctm (isSet⊢c M M₁ x y i i₁) = {!   !}
    ctm (ret x) = {!   !}
    --ctm (bind M M₁) = {!   !}
    ctm (force x) = {!   !}

  GS : CBPVGlobalSection L 
  GS .fst .Section.F-obᴰ = vty
  GS .fst .Section.F-homᴰ = vtm
  GS .fst .Section.F-idᴰ = LV.isProp≤ _ _
  GS .fst .Section.F-seqᴰ _ _ = LV.isProp≤ _ _
  GS .snd .fst .Section.F-obᴰ = cty
  GS .snd .fst .Section.F-homᴰ = ktm
  GS .snd .fst .Section.F-idᴰ = LC.isProp≤ _ _
  GS .snd .fst .Section.F-seqᴰ _ _ = LC.isProp≤ _ _
  GS .snd .snd = ctm
