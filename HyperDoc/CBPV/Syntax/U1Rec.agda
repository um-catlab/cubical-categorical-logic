{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.CBPV.Syntax.U1Rec where

open import Cubical.Data.FinData
open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor 
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.CBPV.TypeStructure

open Alg
open AlgHom
open Category
open Functor
open PshHom
open PshIso
open Signature

module Syntax (Σ : Signature) where 

  Σδ : Signature
  Σδ .Op = Unit ⊎ Σ .Op
  Σδ .arity (inl tt) = 1
  Σδ .arity (inr op) = Σ .arity op

  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy

    data CTy : Type where 
      Ans : CTy

  data _⊢v_ : (A A' : VTy) → Type 
  data _⊢c_ : (A : VTy)(B : CTy) → Type 
  data _⊢k_ : (B B' : CTy) → Type 

  subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  force' :  ∀{B} → U B ⊢c B

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
    thunk : {A : VTy}{B : CTy} → (M : A ⊢c B) → A ⊢v U B
    Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V
    tt : ∀{A} → A ⊢v 𝟙
    η𝟙 : ∀{A} → (V : A ⊢v 𝟙) → tt ≡ V

  data _⊢k_ where
    -- category 
    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    hole : ∀ {B} → B ⊢k B
    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
    isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

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

    -- algebra structure
    ops : ∀(A : VTy)(B : CTy)(op : Σδ .Op) →  
      (Fin (Σδ .arity op) → A ⊢c B) → A ⊢c B
    opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Σδ .Op) →  
      (args : Fin (Σδ .arity op) → A' ⊢c B) → 
      subC V (ops A' B op args) ≡ ops A B op (λ x → subC V (args x))
    opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Σδ .Op) →  
      (args : Fin (Σδ .arity op) → A ⊢c B) → 
      plug S (ops  A B op args) ≡ ops A B' op (λ x → plug S (args x))

    -- type structure
    force : {B : CTy} → U B ⊢c B      
    yes : 𝟙 ⊢c Ans 
    no : 𝟙 ⊢c Ans 
    Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

    -- recursion 
    --δ : ∀ {A B} → A ⊢c B → A ⊢c B
    fix : {B : CTy} → U B ⊢c B → 𝟙 ⊢c B
    unfold : {B : CTy}{M : U B ⊢c B} → 
      fix M ≡ subC (thunk (ops 𝟙 B (inl tt) λ x → fix M)) M 

  subC' = subC
  force' = force

module SyntacticModel (Σ : Signature)  where 
  open Syntax Σ


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

  FreeCompAlg : VTy → CTy → Alg Σδ
  FreeCompAlg A B .Carrier = A ⊢c B , isSet⊢c
  FreeCompAlg A B .interp = ops A B
  
  O : Functor (V ^op ×C C) (ALG Σδ) 
  O .F-ob (A , B) = FreeCompAlg A B
  O .F-hom (V , S) .carmap M = plug S (subC V M)
  O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
  O .F-id = AlgHom≡ (funExt λ M → plugId ∙ subCId)
  O .F-seq (V , S)(V' , S') = AlgHom≡ (funExt λ M → sym plugDist ∙ cong₂ plug refl (sym plugSub ∙ sym subDist ∙ cong₂ subC refl plugSub))

  SynModel : CBPVModel Σδ 
  SynModel .CBPVModel.V = V
  SynModel .CBPVModel.C = C
  SynModel .CBPVModel.O = O 

  open TypeStructure SynModel

  has𝟙 : HasV𝟙 
  has𝟙 .fst = 𝟙
  has𝟙 .snd .trans .N-ob = λ c _ → tt
  has𝟙 .snd .trans .N-hom _ _ _ _ = refl
  has𝟙 .snd .nIso A .fst tt = tt
  has𝟙 .snd .nIso A .snd .fst tt = refl
  has𝟙 .snd .nIso A .snd .snd = η𝟙

  hasUTy : HasUTy
  hasUTy B .fst = U B
  hasUTy B .snd .trans .N-ob A V = subC V force
  hasUTy B .snd .trans .N-hom A A' V W = sym subDist ∙ sym plugId
  hasUTy B .snd .nIso A .fst = thunk
  hasUTy B .snd .nIso A .snd .fst M = Uβ
  hasUTy B .snd .nIso A .snd .snd V = Uη

{-}
module Recursor {Σ : Signature} (M : CBPVModel Σ)where 
  open Syntax Σ 
  open SyntacticModel Σ using (SynModel)
  open CBPVModel
  open TypeStructure M
  module M = CBPVModel M


  module _ (hasV𝟙 : HasV𝟙)(hasUTy : HasUTy) where 
    module Usyn = USyntax hasUTy
    module 𝟙syn = 𝟙Syntax hasV𝟙

    record InterpGen : Type where 
      field  
        interp-Ans : M.C .ob
        interp-yes interp-no : M.O'[ 𝟙syn.𝟙 , interp-Ans ]

    module _ (int : InterpGen) where 
      open InterpGen int

      mutual
        vty : V SynModel .ob → V M .ob
        vty 𝟙 = 𝟙syn.𝟙
        vty (U B) = Usyn.U (cty B)

        cty : C SynModel .ob → C M .ob 
        cty Ans = interp-Ans

      mutual
        vtm : ∀{A A'} → V SynModel [ A , A' ] → V M [ vty A , vty A' ]
        vtm (subV V₁ V₂) = (V M ⋆ vtm V₁) (vtm V₂)
        vtm var = V M .id
        vtm (subVIdl V₁ i) = V M .⋆IdL (vtm V₁) i
        vtm (subVIdr V₁ i) =  V M .⋆IdR (vtm V₁) i
        vtm (subVAssoc V₁ V₂ V₃ i) = V M .⋆Assoc (vtm V₁) (vtm V₂) (vtm V₃) i
        vtm (isSet⊢v V₁ V₂ x y i i₁) = V M .isSetHom (vtm V₁) (vtm V₂) (cong vtm x) (cong vtm y) i i₁
        vtm (thunk M) = Usyn.thunk (ctm M)
        vtm (Uη {A}{B}{V} i) = Usyn.Uη {vty A}{cty B}{vtm V} i
        vtm tt = 𝟙syn.tt
        vtm (η𝟙 {A} V i) = 𝟙syn.𝟙η {vty A}{vtm V} i

        ktm : ∀{B B'} →  C SynModel [ B , B' ] → C M [ cty B , cty B' ]
        ktm (kcomp S S₁) = (C M ⋆ ktm S) (ktm S₁)
        ktm hole = C M .id
        ktm (kcompIdl S i) = C M .⋆IdL (ktm S) i
        ktm (kcompIdr S i) = C M .⋆IdR (ktm S) i
        ktm (kcompAssoc S S₁ S₂ i) = C M .⋆Assoc (ktm S) (ktm S₁) (ktm S₂) i
        ktm (isSet⊢k S S₁ x y i i₁) = C M .isSetHom (ktm S) (ktm S₁) (cong ktm x) (cong ktm y) i i₁

        ctm : ∀{A B} → A ⊢c B → fst (F-ob (O M) (vty A , cty B) .Alg.Carrier)
        ctm (subC V N) = M.lcomp (vtm V) .carmap (ctm N)
        ctm (plug S N) = M.rcomp (ktm S) .carmap (ctm N)
        ctm (plugId {A}{B}{M} i) = M.lcompId {vty A}{cty B}{ctm M} i
        ctm (subCId {A}{B}{M} i) = M.rcompId {vty A}{cty B}{ctm M} i
        ctm (plugDist {A}{B}{B'}{B''}{S}{S'}{M} i) = M.rcompSeq {vty A}{cty B}{cty B'}{cty B''}{ktm S}{ktm S'}{ctm M} i
        ctm (subDist {A}{A'}{A''}{B}{V}{V'}{M} i) = M.lcompSeq {vty A}{vty A'}{vty A''}{cty B}{vtm V}{vtm V'}{ctm M} i
        ctm (plugSub {A}{A'}{B}{B'}{V}{M}{S} i) = M.lrSeq {vty A}{vty A'}{cty B}{cty B'}{vtm V}{ctm M}{ktm S} i
        ctm (isSet⊢c M M₁ x y i i₁) = {! M.O .F-hom ? .carmap ?   !}
        ctm (ops A B op args) = M.O .F-ob ((vty A) , (cty B)) .interp op λ a → ctm{A}{B} (args a)
        ctm (opsSub V op args i) = {! M.O .F-ob ?  .interp  !}
        ctm (opsPlug S op args i) = {!   !}
        ctm force = Usyn.force
        ctm yes = interp-yes
        ctm no = interp-no
        ctm (Uβ {A}{B}{M} i) = Usyn.Uβ {vty A}{cty B}{ctm M} i
        ctm (δ M) = {!   !}
        ctm (fix M) = {!   !}
        ctm (unfold {B}{M} i) = {!   !}

      FV : Functor (V SynModel) (V M)
      FV .F-ob = vty
      FV .F-hom = vtm
      FV .F-id = refl
      FV .F-seq _ _ = refl


      FC : Functor (C SynModel) (C M)
      FC .F-ob = cty
      FC .F-hom = ktm
      FC .F-id = refl
      FC .F-seq _ _ = refl

      FO : NatTrans (O SynModel) (O M ∘F ((FV ^opF) ×F FC))
      FO .NatTrans.N-ob (A , B) .AlgHom.carmap = ctm {A}{B}
      FO .NatTrans.N-ob (A , B) .AlgHom.pres op args = refl
      FO .NatTrans.N-hom f = AlgHom≡ (funExt λ M → {!   !})
      
      M-rec : CBPVMorphism SynModel M 
      M-rec .CBPVMorphism.FV = FV
      M-rec .CBPVMorphism.FC = FC
      M-rec .CBPVMorphism.FO = FO
-}