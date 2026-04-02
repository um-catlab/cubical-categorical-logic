{-# OPTIONS --type-in-type #-}

module HyperDoc.Operational.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor

open import HyperDoc.Operational.TransitionSystemAlt

open Category
open Functor

mutual 
  data VTy : Type where 
    𝟙 : VTy

  data CTy : Type where 
    Ans : CTy

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

  -- type structure
  yes : 𝟙 ⊢c Ans 
  no : 𝟙 ⊢c Ans 

subC' = subC

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

open import HyperDoc.Operational.Model
open import HyperDoc.Operational.TransitionSystemAlt
open import Cubical.Data.Sigma
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.More
open import Cubical.Data.Unit
open TSystem 
open TSystem[_,_] 

-- these are our only obligations.. 
step : (A : VTy)(B : CTy) → A ⊢c B → Maybe (A ⊢c B) 
step = {!   !}

f' : ∀{A A' B B'} → (V : A' ⊢v A) (S : B ⊢k B') (M : A ⊢c B) → A' ⊢c B'
f' V S M = subC V (plug S M)

comm' : ∀{A A' B B'} → (V : A' ⊢v A) (M : A ⊢c B) (S : B ⊢k B') →
  map-Maybe (f' V S ) (step A B M) 
  ≤ 
  step A' B' (f' V S M)
comm' {A}{A'}{B}{B'} V M S with (step A B M) 
... | nothing = tt*
... | just M' = goal where 
  {- 
      we have (step A B M) ↦ just M' 
      the RHS Must step, else we have false
      say step A' B' (f' M) ↦ just N
      then it must be the case that 
      f' M' ≡ N
      in summary 

      V ◁ (step M) ▷ S ≡ step (V ◁ M ▷ S)
  -}
  goal : just (subC V (plug S M')) ≤ step A' B' (subC V (plug S M)) 
  goal = {!   !}

-- forcing deterministic reduction with out definition of TSystem
Sys : (A : VTy)(B : CTy) → TSystem _
Sys A B .state = (A ⊢c B) , isSet⊢c
Sys A B .trans = step A B

SysH : ∀{A A' B B'} → A' ⊢v A → B ⊢k B' → TSysCat [ Sys A B , Sys A' B' ] 
SysH V S .tmap M = f' V S M
SysH V S .comm {M} = comm' V M S

O : Functor ((V ^op) ×C C) TSysCat
O .F-ob (A , B) = Sys A B
O .F-hom {(A , B)}{(A' , B')} (V , S) = SysH V S
O .F-id = TSysMap≡ (funExt λ M → subCId ∙ plugId) 
O .F-seq (V , S) (V' , S') = TSysMap≡ (funExt λ M → sym subDist ∙ cong₂ subC refl (cong₂ subC refl (sym plugDist) ∙ plugSub)) 

Syn : CBPVModel 
Syn .CBPVModel.V = V
Syn .CBPVModel.C = C
Syn .CBPVModel.O = O