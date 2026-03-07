{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.UF1 where 

open import Cubical.Data.List 
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.FinData

import Cubical.Data.Equality as Eq

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib
open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Operational.TypeStructure

open Category
open Functor
open AlgHom
open Alg
open Signature

module Syntax
  (Σ : Signature)
 where

  mutual 
    data VTy : Type  where 
      𝟙 Ans : VTy 
      U : CTy → VTy 

    data CTy : Type  where
      F : VTy → CTy    

  data _⊢v_ : (A A' : VTy) → Type  
  data _⊢c_ : (A : VTy)(B : CTy) → Type  
  data _⊢k_ : (B B' : CTy) → Type  

  data _⊢v_   where
    var : ∀{A}  → A ⊢v A
    tt : ∀{A} → A ⊢v 𝟙
    yes : ∀{A} → A ⊢v Ans 
    no : ∀{A} → A ⊢v Ans 
    thunk : ∀{A B} → A ⊢c B → A ⊢v U B

   -- isSet⊢v : ∀{A A'} → isSet (A ⊢v A')



  data _⊢c_ where   
    ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
    -- ops don't fit into first arg
    bind : ∀{A A' B} → A ⊢c F A' → A' ⊢c B → A ⊢c B
    force : ∀{A B} →  A ⊢v U B → A ⊢c B    
    -- algebra structure
    ops : ∀{A B} → (op : Σ .Op) →  
      (Fin (Σ .arity op) → A ⊢c B) → A ⊢c B
    --isSet⊢c : ∀{A B} → isSet (A ⊢c B)

  data _⊢k_ where 
    hole : ∀{B} → B ⊢k B
    bindk : ∀{A B B'} → B ⊢k F A → A ⊢c B' → B ⊢k B'
   -- isSet⊢k : ∀{B B'} → isSet (B ⊢k B')


  mutual 
    subV : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subV V var = V
    subV V tt = tt
    subV V yes = yes
    subV V no = no
    subV V (thunk M) = thunk (subC V M)
   -- subV V (isSet⊢v W W' x y i i₁) = (isSet⊢v (subV V W) (subV V W') (cong₂ subV refl x) (cong₂ subV refl y)  i i₁)

    subC : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subC V (ret W) = ret (subV V W)
    subC V (bind M N) = bind (subC V M) N
    subC V (force W) = force (subV V W)
    subC V (ops op args) = ops op λ x → subC V (args x)
    --subC V (isSet⊢c M M' x y i i₁) = (isSet⊢c (subC V M) (subC V M') (cong₂ subC refl x) (cong₂ subC refl y) i i₁)

    plug : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B'
    plug hole M = M
    plug (bindk S M) N = bind (plug S N) M
    -- plug (isSet⊢k S S' x y i i₁) M = (isSet⊢c (plug S M) (plug S' M) (cong₂ plug x refl) (cong₂ plug y refl)  i i₁)

    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    kcomp S hole = S
    kcomp S (bindk S' M) = bindk (kcomp S S') M
   -- kcomp S (isSet⊢k S' S'' x y i i₁) = (isSet⊢k (kcomp S S') (kcomp S S'') (cong₂ kcomp refl x) (cong₂ kcomp refl y) i i₁) 

    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdl var = refl
    subVIdl tt = refl
    subVIdl yes = refl
    subVIdl no = refl
    subVIdl (thunk M) = cong thunk (subCId M)
   -- subVIdl (isSet⊢v V V₁ x y i i₁) = {!  isSet⊢v  !}
      -- isSet⊢v  (subVIdl V j) (subVIdl V₁ j) (λ j' → subVIdl (x j') j) (λ j' → subVIdl (y j') j) i i₁

    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)
    subVAssoc V W var = refl
    subVAssoc V W tt = refl
    subVAssoc V W yes = refl
    subVAssoc V W no = refl
    subVAssoc V W (thunk M) = cong thunk (sym (subDist V W M))
   -- subVAssoc V W (isSet⊢v Y Y₁ x y i i₁) = {!   !}

    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVIdr V = refl

    subCId : ∀ {A B}(M : A ⊢c B) → subC (var {A}) M ≡ M
    subCId (ret V) = cong ret (subVIdl V)
    subCId (bind M N) = cong₂ bind (subCId M) refl
    subCId (force V) = cong force (subVIdl V)
    subCId (ops op args) i = ops op λ x → subCId (args x) i
   -- subCId (isSet⊢c M M₁ x y i i₁) = {!   !}

    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdl hole = refl
    kcompIdl (bindk M x) = cong₂ bindk (kcompIdl M) refl
   -- kcompIdl (isSet⊢k M M₁ x y i i₁) = {!   !}

    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompIdr M = refl

    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)
    kcompAssoc M N hole = refl
    kcompAssoc M N (bindk P x) = cong₂ bindk (kcompAssoc M N P) refl
    --kcompAssoc M N (isSet⊢k P P₁ x y i i₁) = {!   !}

    plugId : ∀ {A B}(M : A ⊢c B) → plug (hole {B}) M ≡ M
    plugId M = refl

    plugDist : ∀ {A B B' B''}(S : B ⊢k B')(S' : B' ⊢k B'')(M : A ⊢c B) → 
      plug S' (plug S M) ≡ plug (kcomp S S') M
    plugDist S hole M = refl
    plugDist S (bindk S' x) M = cong₂ bind (plugDist S S' M) refl
    --plugDist S (isSet⊢k S' S'' x y i i₁) M = {!   !}

    subDist : ∀ {A A' A'' B}(V : A ⊢v A')(V' : A' ⊢v A'')(M : A'' ⊢c B) → --lcomp
      subC V (subC V' M) ≡ subC (subV V V') M
    subDist V V' (ret x) = cong ret (sym (subVAssoc V V' x ))
    subDist V V' (bind M M₁) = cong₂ bind (subDist V V' M) refl
    subDist V V' (force x) = cong force (sym (subVAssoc V V' x ))
    subDist V V' (ops op args) i = ops op λ x → (subDist V V' (args x)) i
    --subDist V V' (isSet⊢c M M₁ x y i i₁) = {!   !}
  
    plugSub : ∀ {A A' B B'}(V : A ⊢v A')(M : A' ⊢c B)(S : B ⊢k B') → 
      subC V (plug S M) ≡ plug S (subC V M)
    plugSub V M hole = refl
    plugSub V M (bindk S x) = cong₂ bind (plugSub V M S) refl
   -- plugSub V M (isSet⊢k S S₁ x y i i₁) = {!   !}

    opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Σ .Op) →  
      (args : Fin (Σ .arity op) → A' ⊢c B) → 
      subC V (ops {A'} {B} op args) ≡ ops {A} {B} op (λ x → subC V (args x))
    opsSub V op args = refl
{-
    opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Σ .Op) →  
      (args : Fin (Σ .arity op) → A ⊢c B) → 
      plug S (ops {A} {B} op args) ≡ ops {A} {B'} op (λ x → plug S (args x))
    opsPlug hole op args = refl
    opsPlug (bindk S M) op args = cong₂ bind (opsPlug S op args) refl ∙ {!  refl !} -}
    {-
      this requires
      bind (ops op (λ x → plug S (args x))) M ≡
      ops op (λ x → bind (plug S (args x)) M)

      which seems like a requirement we need to demand
    -}

    -- Operational Semantics 
    {-
      what are terminals when we have opaque operations ..?
      can we evaluate under op?
      if these are algebraic effects.. can't we just "pull all op to the top"?
        ex
          bind M (boop ; N) = boop ; bind M N
      but this is the equation we dont have
          
    -}
    -- define CBPVMorphism into transition system model
    red : {!   !}
    red = {!   !}


module SyntacticModel (Σ : Signature)  where 
  open Syntax Σ

  module _ 
      -- operations are algebraic
      (opsPlug :  
        ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')
        (op : Σ .Op) →  
        (args : Fin (Σ .arity op) → A ⊢c B) → 
        plug S (ops {A} {B} op args) 
          ≡ 
        ops {A} {B'} op (λ x → plug S (args x))) where 

    V : Category ℓ-zero ℓ-zero
    V .ob = VTy
    V .Hom[_,_] = _⊢v_
    V .id = var
    V ._⋆_ = subV
    V .⋆IdL = subVIdl
    V .⋆IdR = subVIdr
    V .⋆Assoc = subVAssoc
    V .isSetHom = {!   !}

    C : Category ℓ-zero ℓ-zero 
    C .ob = CTy
    C .Hom[_,_] = _⊢k_
    C .id = hole
    C ._⋆_ = kcomp
    C .⋆IdL = kcompIdl
    C .⋆IdR = kcompIdr
    C .⋆Assoc = kcompAssoc
    C .isSetHom = {!   !}

    FreeCompAlg : VTy → CTy → Alg Σ
    FreeCompAlg A B .Carrier = A ⊢c B , {!   !}
    FreeCompAlg A B .interp = ops {A}{B}
    
    O : Functor (V ^op ×C C) (ALG Σ) 
    O .F-ob (A , B) = FreeCompAlg A B
    O .F-hom (V , S) .carmap M = plug S (subC V M)
    O .F-hom (V , S) .pres op args = cong (λ h →  plug S h) (opsSub V op args) ∙ opsPlug S op λ x → subC V (args x)
    O .F-id = AlgHom≡ (funExt λ M → (plugId (subC var M)) ∙ (subCId M))
    O .F-seq (W , S)(V' , S') = 
      AlgHom≡ (funExt λ M → 
        sym (plugDist S S' (subC (subV V' W) M) ) 
        ∙ cong₂ plug (refl {x = S'}) (sym (plugSub (subV V' W) M S) ∙ sym (subDist V' W (plug S M) ) ∙ cong₂ subC (refl {x = V'}) (plugSub W M S)))

    SynModel : CBPVModel Σ 
    SynModel .CBPVModel.V = V
    SynModel .CBPVModel.C = C
    SynModel .CBPVModel.O = O 

    open TypeStructure SynModel 

    hasV𝟙 : HasV𝟙 
    hasV𝟙 A .fst = 𝟙
    hasV𝟙 A .snd .fst V = tt
    hasV𝟙 A .snd .snd tt = tt

    hasFTy : HasFTy 
    hasFTy A B .fst = F A
    -- A ⊢c B → F A ⊢k B
    hasFTy A B .snd .fst M = bindk hole M
    -- F A ⊢k B → A ⊢c B
    hasFTy A B .snd .snd S = plug S (ret var)

    hasUTy : HasUTy
    hasUTy A B .fst = U B
    hasUTy A B .snd .fst = thunk
    hasUTy A B .snd .snd = force