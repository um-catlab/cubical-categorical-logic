{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Syntax where

open import Cubical.Data.Sigma
open import Cubical.Data.FinData

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor

open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Effects.Model
open import HyperDoc.Operational.Effects.BiAlgebra

open Category
open Functor
open Signature

module Syntax (Sig : Signature) where 
  mutual 
    data VTy : Type where 
      𝟙 : VTy
      U : CTy → VTy 
      _⊕_ : VTy → VTy → VTy 

    data CTy : Type where 
      F : VTy → CTy

  𝟚 = 𝟙 ⊕ 𝟙 
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
    subtt : ∀ {A A'} {V : A ⊢v A'} → tt ≡ subV V tt

    thunk : ∀{A B} → A ⊢c B → A ⊢v U B

    σ₁ : ∀ {A A'} → A ⊢v (A ⊕ A')
    σ₂ : ∀ {A A'} → A' ⊢v (A ⊕ A') 


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

    -- Effects
    ops : ∀{A : VTy}{B : CTy}(op : Sig .Op) →  
      (Fin (Sig .arity op) → A ⊢c B) → A ⊢c B
    
    opsSub : ∀{A A' : VTy}{B : CTy}(V : A ⊢v A')(op : Sig .Op) →  
      (args : Fin (Sig .arity op) → A' ⊢c B) → 
      subC V (ops op args) ≡ ops op (λ x → subC V (args x))
    
    opsPlug :  ∀{A : VTy}{B B' : CTy}(S : B ⊢k B')(op : Sig .Op) →  
      (args : Fin (Sig .arity op) → A ⊢c B) → 
      plug S (ops op args) ≡ ops op (λ x → plug S (args x))
    
    -- type structure
    ret : ∀{A B} → F A ⊢k B → A ⊢c B
    ret-sub : ∀ {A B B'}{S : B ⊢k B'}{S' : F A ⊢k B} → 
      ret (kcomp S' S) ≡ plug S (ret S')

    force : ∀{A B} →  A ⊢v U B → A ⊢c B   
    force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
      force (subV V W) ≡ subC V (force W) 

    match : ∀ {A A' B} → (A ⊢c B) → (A' ⊢c B) → (A ⊕ A') ⊢c B
    plugmatch : ∀ {A A' B B'}{S : B ⊢k B'}{M : A ⊢c B}{N : A' ⊢c B} → 
      match (plug S M) (plug S N) ≡ plug S (match M N)

  true : ∀ {Γ} → Γ ⊢v 𝟚 
  true = subV tt σ₁

  false : ∀ {Γ} → Γ ⊢v 𝟚 
  false = subV tt σ₂

  subC' = subC

  ret' : {A A' : VTy} → A ⊢v A' → A ⊢c F A' 
  ret' V = subC V (ret hole)

  x←_,,_ : {Γ A : VTy}{B : CTy} → Γ ⊢c F A → A ⊢c B → Γ ⊢c B 
  x←_,,_ M N = plug (bind N) M

  _[_/x] : ∀ {Γ A B} → A ⊢c B → Γ ⊢v A → Γ ⊢c B 
  M [ V /x] = subC V M

  _[_/•] : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B' 
  S [ M /•] = plug S M

  data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
    βrefl : ∀{A B}{M : A ⊢c B} → 
      --------
      M ↦ M
    Fβ : ∀{A B}{M : A ⊢c B} → 
      -------------------
      ret (bind M) ↦ M

    Uβ : ∀ {A B} {M : A ⊢c B} → 
      ---------------------
      force (thunk M) ↦ M

    +β₁ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
      subC σ₁ (match M N) ↦ M

    +β₂ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
      subC σ₂ (match M N) ↦ N

    alg-cong : ∀ 
      {A B op}
      {args args'  : Fin (Sig .arity op) → A ⊢c B} → 
      (∀ (i : Fin (Sig .arity op)) → args i ↦ args' i) → 
      ---------------------
      ops op args ↦ ops op args'
    
    subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      (M [ V /x])  ↦ (M' [ V /x])

    plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
      M ↦ M' → 
      --------- 
      (S [ M /•]) ↦ (S [ M' /•]) 
    isProp↦ : ∀ {A B} {M M' : A ⊢c B} → isProp (M ↦ M')

module SynModel (Sig : Signature) where 
  open Syntax Sig
  open import HyperDoc.Operational.Graph

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
  open BifunctorSep

  open Alg
  open BiAlg
  open BiAlgHom

  bialg : VTy → CTy → BiAlg Sig
  bialg A B .car = (A ⊢c B) , isSet⊢c
  bialg A B .isAlg = ops
  bialg A B .isRGraph .fst M M' = (M ↦ M') , isProp↦
  bialg A B .isRGraph .snd M = βrefl
  bialg A B .congruence op args args' = alg-cong

  leftAction : ∀ {A A' B} → A' ⊢v A →  BIALG Sig [ bialg A B , bialg A' B ]
  leftAction V .map M = subC V M
  leftAction V .isAlgHom op args = opsSub V op args
  leftAction V .isRelator .fst M↦M' = subC-cong M↦M'
  leftAction V .isRelator .snd = isProp↦ _ _

  rightAction : ∀ {A B B'} → B ⊢k B' → BIALG Sig [ bialg A B , bialg A B' ] 
  rightAction S .map M = plug S M
  rightAction S .isAlgHom op args = opsPlug S op args
  rightAction S .isRelator .fst M↦M' = plug-cong M↦M'
  rightAction S .isRelator .snd = isProp↦ _ _

  O : BifunctorSep (V ^op) C  (BIALG Sig)
  O .Bif-ob = bialg
  O .Bif-homL V B = leftAction V
  O .Bif-L-id = BiAlgHom≡ (funExt λ M → subCId)
  O .Bif-L-seq _ _ = BiAlgHom≡ (funExt λ M → sym subDist)
  O .Bif-homR B S = rightAction S
  O .Bif-R-id = BiAlgHom≡  (funExt λ M → plugId)
  O .Bif-R-seq _ _ = BiAlgHom≡ (funExt λ  M  → sym plugDist)
  O .SepBif-RL-commute _ _ = BiAlgHom≡  (funExt λ M → plugSub) 
  
  Syn : CBPVModel Sig
  Syn .fst = V
  Syn .snd .fst = C
  Syn .snd .snd = O

  open import HyperDoc.Operational.Effects.TypeStructure  
  open import Cubical.Categories.Presheaf.Morphism.Alt
  open PshHom
  open TypeStructure Syn

  open WkRepresentation
  open import Cubical.Categories.NaturalTransformation
  open NatTrans
  open import Cubical.Data.Unit

  has𝟙 : Has𝟙 
  has𝟙 .fst = 𝟙
  has𝟙 .snd .N-ob A tt = tt
  has𝟙 .snd .N-hom V = funExt λ {tt → subtt}

  has+ : Has+ 
  has+ A A' .TypeStructure.Has+'.A+A' = A ⊕ A'
  has+ A A' .TypeStructure.Has+'.match .N-ob B (M , N) = match M N
  has+ A A' .TypeStructure.Has+'.match .N-hom S = funExt λ (M , N) → plugmatch
  has+ A A' .TypeStructure.Has+'.σ₁ = σ₁
  has+ A A' .TypeStructure.Has+'.σ₂ = σ₂
  has+ A A' .TypeStructure.Has+'.+β₁ M N = +β₁
  has+ A A' .TypeStructure.Has+'.+β₂ M N = +β₂

  hasUTy : HasUTy 
  hasUTy B .rep = U B
  hasUTy B .fwd .N-ob A = force
  hasUTy B .fwd .N-hom V = funExt λ V' → force-sub
  hasUTy B .bkwd = thunk
  hasUTy B .wkretract M = Uβ

  hasFTy : HasFTy 
  hasFTy A .rep = F A
  hasFTy A .fwd .N-ob B = ret
  hasFTy A .fwd .N-hom {B}{B'}S = funExt λ S' → ret-sub
  hasFTy A .bkwd = bind
  hasFTy A .wkretract M = Fβ
