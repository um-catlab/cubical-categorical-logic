{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc

module HyperDoc.CBPV.Syntax.UF1 where 

open import Cubical.Data.FinData
open import Cubical.Data.Unit

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor 
open import Cubical.Categories.Presheaf.Morphism.Alt hiding (_∘ˡ_)

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

  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy
      Ans : VTy

    data CTy : Type where 
      F : VTy → CTy

  data _⊢v_ : (A A' : VTy) → Type 
  data _⊢c_ : (A : VTy)(B : CTy) → Type 
  data _⊢k_ : (B B' : CTy) → Type 

  subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  force' :  ∀{B} → U B ⊢c B
  plug' : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'
  ret' : {A : VTy} → A ⊢c F A

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
    
    yes : 𝟙 ⊢v Ans 
    no : 𝟙 ⊢v Ans 

  data _⊢k_ where
    -- category 
    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    hole : ∀ {B} → B ⊢k B
    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
    isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

    -- type structure
    bind : {A : VTy}{B : CTy} → A ⊢c B → F A ⊢k B
    Fη : ∀ {A B}{S : F A ⊢k B} → bind (plug' S ret') ≡ S

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
    ops : ∀(A : VTy)(B : CTy)(op : Σ .Op) →  
      (Fin (Σ .arity op) → A ⊢c B) → A ⊢c B
    opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Σ .Op) →  
      (args : Fin (Σ .arity op) → A' ⊢c B) → 
      subC V (ops A' B op args) ≡ ops A B op (λ x → subC V (args x))
    opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Σ .Op) →  
      (args : Fin (Σ .arity op) → A ⊢c B) → 
      plug S (ops  A B op args) ≡ ops A B' op (λ x → plug S (args x))

    -- type structure
    force : {B : CTy} → U B ⊢c B    
    Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

    ret : {A : VTy} → A ⊢c F A
    Fβ : ∀{A B}{M : A ⊢c B} →  plug (bind M) ret ≡ M


  subC' = subC
  force' = force
  plug' = plug
  ret' = ret



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

  FreeCompAlg : VTy → CTy → Alg Σ
  FreeCompAlg A B .Carrier = A ⊢c B , isSet⊢c
  FreeCompAlg A B .interp = ops A B
  
  O : Functor (V ^op ×C C) (ALG Σ) 
  O .F-ob (A , B) = FreeCompAlg A B
  O .F-hom (V , S) .carmap M = plug S (subC V M)
  O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
  O .F-id = AlgHom≡ (funExt λ M → plugId ∙ subCId)
  O .F-seq (V , S)(V' , S') = AlgHom≡ (funExt λ M → sym plugDist ∙ cong₂ plug refl (sym plugSub ∙ sym subDist ∙ cong₂ subC refl plugSub))

  SynModel : CBPVModel Σ 
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

  hasFTy : HasFTy 
  hasFTy A .fst = F A
  hasFTy A .snd .trans .N-ob B S = plug S ret
  hasFTy A .snd .trans .N-hom B B' S S' = sym plugDist ∙ cong₂ plug refl (sym subCId)
  hasFTy A .snd .nIso B .fst = bind
  hasFTy A .snd .nIso B .snd .fst M = Fβ
  hasFTy A .snd .nIso B .snd .snd S = Fη
