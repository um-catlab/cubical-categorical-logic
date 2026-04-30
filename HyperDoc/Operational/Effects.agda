{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor


open import HyperDoc.Operational.Graph
open import HyperDoc.Algebra.Algebra

open Category
open Functor

module _ 


{-}

{-}
data ETy : Type where 
  𝟘 𝟙 : ETy 
  _+s_ : ETy → ETy → ETy 

Univ : Type 
Univ = ETy → Type

Sig : Type 
Sig = Σ[ Op ∈ Type ] ((op : Op) → ETy × ETy)


data StoreOps : Type where 
  read write : StoreOps

--Store : Sig 
--Store .fst = StoreOps
--Store .snd read = 𝟙 , nat
--Store .snd write = nat , 𝟙
-}

mutual 
  data VTy : Type where 
    𝟙 : VTy
    -- Ans : VTy
    U : CTy → VTy 
    _⊗_ _⊕_ : VTy → VTy → VTy 

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

  _,p_ : ∀ {A A' A''} → A ⊢v A' → A ⊢v A'' → A ⊢v (A' ⊗ A'')
  sub,p : ∀ {X Y Z Z'} {V : X ⊢v Y}{W : Y ⊢v Z}{W' : Y ⊢v Z'} → 
    (subV V W ,p subV V W') ≡ subV V (W ,p W')

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

  -- Hardcoded Store Signature
  read : ∀ {A B} → A ⊢v 𝟙 → 𝟚 ⊢c B → A ⊢c B 
  write : ∀ {A B} → A ⊢v 𝟚 → 𝟙 ⊢c B → A ⊢c B
  
  -- type structurer
  ret : ∀{A B} → F A ⊢k B → A ⊢c B
  ret-sub : ∀ {A B B'}{S : B ⊢k B'}{S' : F A ⊢k B} → 
    ret (kcomp S' S) ≡ plug S (ret S')
  -- ret : ∀{A} → A ⊢c F A
  -- force : ∀{B} →  U B ⊢c B  
  force : ∀{A B} →  A ⊢v U B → A ⊢c B   
  force-sub : ∀{A A' B}{V : A' ⊢v A}{W : A ⊢v U B} → 
    force (subV V W) ≡ subC V (force W) 


  match : ∀ {A A' B} → (A ⊢c B) → (A' ⊢c B) → (A ⊕ A') ⊢c B
  plugmatch : ∀ {A A' B B'}{S : B ⊢k B'}{M : A ⊢c B}{N : A' ⊢c B} → 
    match (plug S M) (plug S N) ≡ plug S (match M N)

subC' = subC

rec× : ∀ {Γ A A' B} → Γ ⊢v (A ⊗ A') → (A ⊗ A') ⊢c B → Γ ⊢c B 
rec× p m = subC p m

import  Cubical.Data.Equality as Eq


data _↦_ : {A : VTy}{B : CTy} → A ⊢c B → A ⊢c B → Type where 
  Fβ : ∀{A B}{M : A ⊢c B} → 
    ------------------------------------
    ret (bind M)  ↦ M

  Uβ : ∀ {A B} {M : A ⊢c B} → 
    ---------------------
    force (thunk M) ↦ M

  +β₁ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
    subC σ₁ (match M N) ↦ M

  +β₂ : ∀ {A A' B}{M : A ⊢c B}{N : A' ⊢c B} →  
    subC σ₂ (match M N) ↦ N
  
  subC-cong : ∀ {A A' B}{V : A' ⊢v A}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    subC V M  ↦ subC V M'

  plug-cong : ∀ {A B B'}{S : B ⊢k B'}{M M' : A ⊢c B}  →  
    M ↦ M' → 
    --------- 
    plug S M ↦ plug S M'

-}