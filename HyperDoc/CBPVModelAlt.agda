{-# OPTIONS --type-in-type #-}
module HyperDoc.CBPVModelAlt where 

open import Cubical.Data.List using (_∷_ ; [] ; _++_ ;  List)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure 

open import Cubical.Categories.Category 
open import Cubical.Categories.Monad.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.EilenbergMoore
open import Cubical.Categories.Constructions.BinProduct 
open import Cubical.Categories.Instances.FunctorAlgebras
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib
open import HyperDoc.Effects.ManualWriter
open Functor
open Category
open Writer (Unit , isSetUnit)

record Model (ℓV ℓV' ℓC ℓC' ℓS : Level): Type {!   !} where 
  field 
    V : Category ℓV ℓV' 
    C : Category ℓC ℓC' 
    O : Functor ((V ^op) ×C C) (WRITERALG _)

mutual 
  data VTy : Type  _ where 
    one : VTy 
    U : CTy → VTy 

  data CTy : Type _ where
    F : VTy → CTy    

-- TODO
-- adjust the syntax so naturality comes "for free"
data _⊢v_ : (A A' : VTy) → Type _
data _⊢c_ : (A : VTy)(B : CTy) → Type _
data _⊢k_ : (B B' : CTy) → Type _

force' :  ∀{B} → U B ⊢c B
hole' : ∀ {B} → B ⊢k B
kcomp' : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
ret' : ∀{A } → A ⊢c F A
bind' : ∀{A B} → A ⊢c B → F A ⊢k B
subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

data _⊢v_   where
  -- category 
  subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
  var : ∀ {A} → A ⊢v A
  subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
  subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
  subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
    subV (subV V W) Y ≡ subV V (subV W Y)

  -- type structure
  tt : ∀{A} → A ⊢v one
  oneη : ∀{A}{V : A ⊢v one} → tt ≡ V

  thunk : ∀{A B} → A ⊢c B → A ⊢v U B
  Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V

  isSet⊢v : ∀{A A'} → isSet (A ⊢v A')


data _⊢c_ where 
  ret : ∀{A } → A ⊢c F A
  
  subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
  plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'

  Fβ : ∀{A B}{M : A ⊢c B} → M ≡ plug (bind' M) ret
  force : ∀{B} → U B ⊢c B
  Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

  -- interaction laws (profunctor action)
  plugId : ∀ {A B}{M : A ⊢c B} → plug (hole' {B}) M ≡ M
  subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
  plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
    plug S' (plug S M) ≡ plug (kcomp' S S') M
  subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
    subC V (subC V' M) ≡ subC (subV V V') M
  plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
    subC V (plug S M) ≡ plug S (subC V M)

  -- just encode effect
 -- beep : ∀{A B} → A ⊢c B → A ⊢c B
  beep : ∀ {A} → A ⊢c F A 

  isSet⊢c : ∀{A B} → isSet (A ⊢c B)

force' = force

data _⊢k_ where 
  -- category 
  kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
  hole : ∀ {B} → B ⊢k B
  kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
  kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
  kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
    kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)

  -- type structure 
  bind : ∀{A B} → A ⊢c B → F A ⊢k B
  Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug S ret)

 -- beep : ∀{B} → B ⊢k B 

  isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

hole' = hole
kcomp' = kcomp
ret' = ret
bind' = bind
subC' = subC

V : Category _ _ 
V .ob = VTy
V .Hom[_,_] = _⊢v_
V .id = var
V ._⋆_ = subV
V .⋆IdL = subVIdl
V .⋆IdR = subVIdr
V .⋆Assoc = subVAssoc
V .isSetHom = isSet⊢v

C : Category _ _ 
C .ob = CTy
C .Hom[_,_] = _⊢k_
C .id = hole
C ._⋆_ = kcomp
C .⋆IdL = kcompIdl
C .⋆IdR = kcompIdr
C .⋆Assoc = kcompAssoc
C .isSetHom = isSet⊢k

M : Model _ _ _ _ _ 
M .Model.V = V
M .Model.C = C
M .Model.O .F-ob (A , B) = FreeWriterAlg (A ⊢c B)  ,  {!   !}
M .Model.O .F-hom (f , g) = ext _  λ z → ret (plug g (subC f z))
M .Model.O .F-id = {!   !}
M .Model.O .F-seq = {!   !}

_ = {! M .Model.O .F-hom (V .id , ?) .snd !}

beep' : ∀{A B} → A ⊢c B → A ⊢c B 
beep' M = {! subC ? M  !}

beep2 : ∀ {A B} → (WRITERALG _)[ (FreeWriterAlg (A ⊢c B) , {!   !}) , (FreeWriterAlg (A ⊢c B)  , {!   !}) ]
beep2 = ext _ λ M → c* tt (ret M)

plug' : ∀{A B B'} → B ⊢k B' → (WRITERALG _)[ (FreeWriterAlg (A ⊢c B) , {!   !}) , (FreeWriterAlg (A ⊢c B')  , {!   !}) ] 
plug' S = M .Model.O .F-hom (V .id , S)

lemma : ∀{A B B'} → (M : ⟨ FreeWriterAlg (A ⊢c B)⟩ ) → (S : B ⊢k B') → plug' S .fst (beep2 .fst M) ≡ beep2 .fst (plug' S .fst M)
lemma M S = plug' S .snd tt M ∙ {!   !} ∙ sym (beep2 .snd tt ((plug' S .fst M)))
{-}
beep' : ∀{A B} → A ⊢c B → A ⊢c B 
beep' M = plug beep M

beep2 : ∀ {A B} → ⟨ FreeWriterAlg (A ⊢c B) ⟩ → ⟨ FreeWriterAlg (A ⊢c B) ⟩ 
beep2 = ext _ (λ M → c* tt (ret M)) .fst

plug' : ∀ {B B'} → {!   !} 
plug' = {!   !}

true : ∀{A B B' } → (S : B ⊢k B') → (M : A ⊢c B) → plug S (beep' M) ≡ beep' (plug S M) 
true {A}{B}{B'} S M = {! ? ∙  plugDist {A}{B}{B'} {B'' = B'} {S = S} {S' = beep} {M = M} !}
  -- plugDist ∙ {!   !} ∙ sym plugDist

-}

{-}
beep' : ∀{B} → B ⊢k B 
beep' = {!   !}

foo : ∀{A B B' } → (S : B ⊢k B') → (M : A ⊢c B) → plug S {!   !} ≡ {! beep'  !} 
foo = {!   !}

hmm : ∀{A B B' } → (S : B ⊢k B') → (M : A ⊢c B) → plug S (beep M) ≡ beep (plug S M) 
hmm S M = {!M   !}
-}

open import Cubical.Data.Bool

{-}
M : Model _ _ _ _ _ (Bool , isSetBool)
M .Model.V = V
M .Model.C = C
M .Model.O .F-ob (A , B) = Writer.FreeWriterAlg(Bool , isSetBool) (A ⊢c B) , {!   !}
M .Model.O .F-hom {(A , B)}{(A' , B')}(f , g) = Writer.ext (Bool , isSetBool) _  λ M → Writer.ret (plug g (subC f M))
M .Model.O .F-id = Writer.WriterHom≡ _ _ {!   !}
M .Model.O .F-seq = {!   !}
-}

{-}
record Model (ℓV ℓV' ℓC ℓC' ℓS : Level)(T : Functor (SET ℓS)(SET ℓS)): Type {!   !} where 
  field 
    V : Category ℓV ℓV' 
    C : Category ℓC ℓC' 
    O : Functor ((V ^op) ×C C) (AlgebrasCategory T) 

module Syntax
  {ℓV ℓV' ℓC ℓC' ℓS : Level } where


  mutual 
    data VTy : Type (levels (ℓV ∷ ℓC ∷ [])) where 
      one : VTy 
      U : CTy → VTy 

    data CTy : Type (levels (ℓV ∷ ℓC ∷ [])) where
      F : VTy → CTy    

  -- TODO
  -- adjust the syntax so naturality comes "for free"
  data _⊢v_ : (A A' : VTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  data _⊢c_ : (A : VTy)(B : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  data _⊢k_ : (B B' : CTy) → Type (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))

  force' :  ∀{B} → U B ⊢c B
  hole' : ∀ {B} → B ⊢k B
  kcomp' : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
  ret' : ∀{A } → A ⊢c F A
  bind' : ∀{A B} → A ⊢c B → F A ⊢k B
  subC' : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B

  data _⊢v_   where
    -- category 
    subV : ∀ {A A' A''} → A ⊢v A' → A' ⊢v A'' → A ⊢v A''
    var : ∀ {A} → A ⊢v A
    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)

    -- type structure
    tt : ∀{A} → A ⊢v one
    oneη : ∀{A}{V : A ⊢v one} → tt ≡ V

    thunk : ∀{A B} → A ⊢c B → A ⊢v U B
    Uη : ∀{A B}{V : A ⊢v U B} →  thunk (subC' V force') ≡ V

    isSet⊢v : ∀{A A'} → isSet (A ⊢v A')


  data _⊢c_ where 
    ret : ∀{A } → A ⊢c F A
    
    subC : ∀ {A A' B} → A ⊢v A' → A' ⊢c B → A ⊢c B
    plug : ∀ {A B B'} → B ⊢k B' → A ⊢c B → A ⊢c B'

    Fβ : ∀{A B}{M : A ⊢c B} → M ≡ plug (bind' M) ret
    force : ∀{B} → U B ⊢c B
    Uβ : ∀ {A B} → {M : A ⊢c B} → subC (thunk M) force ≡ M

    -- interaction laws (profunctor action)
    plugId : ∀ {A B}{M : A ⊢c B} → plug (hole' {B}) M ≡ M
    subCId : ∀ {A B}{M : A ⊢c B} → subC (var {A}) M ≡ M
    plugDist : ∀ {A B B' B''}{S : B ⊢k B'}{S' : B' ⊢k B''}{M : A ⊢c B} → --rcomp
      plug S' (plug S M) ≡ plug (kcomp' S S') M
    subDist : ∀ {A A' A'' B}{V : A ⊢v A'}{V' : A' ⊢v A''}{M : A'' ⊢c B} → --lcomp
      subC V (subC V' M) ≡ subC (subV V V') M
    plugSub : ∀ {A A' B B'}{V : A ⊢v A'}{M : A' ⊢c B}{S : B ⊢k B'} → 
      subC V (plug S M) ≡ plug S (subC V M)

    -- just encode effect
    beep : one ⊢c F one

    isSet⊢c : ∀{A B} → isSet (A ⊢c B)

  force' = force

  data _⊢k_ where 
    -- category 
    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B''
    hole : ∀ {B} → B ⊢k B
    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡  kcomp M (kcomp N P)

    -- type structure 
    bind : ∀{A B} → A ⊢c B → F A ⊢k B
    Fη : ∀ {A B}{S : F A ⊢k B} → S ≡ bind (plug S ret)

    isSet⊢k : ∀{B B'} → isSet (B ⊢k B')

  hole' = hole
  kcomp' = kcomp
  ret' = ret
  bind' = bind
  subC' = subC


  T : Functor (SET ℓS) (SET ℓS)
  T .F-ob X = (List Unit × X .fst) , {!   !}
  T .F-hom f (xs , a) = xs , (f a)
  T .F-id = refl
  T .F-seq _ _ = refl

  V : Category (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  V .ob = VTy
  V .Hom[_,_] = _⊢v_
  V .id = var
  V ._⋆_ = subV
  V .⋆IdL = subVIdl
  V .⋆IdR = subVIdr
  V .⋆Assoc = subVAssoc
  V .isSetHom = isSet⊢v

  C : Category (ℓ-max ℓV ℓC) (levels (ℓV ∷ ℓV' ∷ ℓC ∷ ℓC' ∷ ℓS ∷ []))
  C .ob = CTy
  C .Hom[_,_] = _⊢k_
  C .id = hole
  C ._⋆_ = kcomp
  C .⋆IdL = kcompIdl
  C .⋆IdR = kcompIdr
  C .⋆Assoc = kcompAssoc
  C .isSetHom = isSet⊢k

  free : (X : hSet ℓS) → Algebra T 
  free X .Algebra.carrier = T .F-ob X
  free X .Algebra.str (xs , (ys , a)) = xs ++ ys , a

  M : Model _ _ _ _ _ T
  M .Model.V = V
  M .Model.C = C
  M .Model.O .F-ob (A , B) = free ((A ⊢c B) , {!   !})
  M .Model.O .F-hom (f , g) .AlgebraHom.carrierHom (xs , h) = xs , (subC f (plug g h))
  M .Model.O .F-hom (f , g) .AlgebraHom.strHom = refl
  M .Model.O .F-id = AlgebraHom≡ T (funExt λ _ → ΣPathP (refl , subCId ∙ plugId))
  M .Model.O .F-seq f g = AlgebraHom≡ T (funExt {!   !})


-}

