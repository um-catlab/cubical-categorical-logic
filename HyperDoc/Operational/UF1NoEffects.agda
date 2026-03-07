{-# OPTIONS --type-in-type #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module HyperDoc.Operational.UF1NoEffects where 

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎) 
open import Cubical.Data.FinData

import Cubical.Data.Equality as Eq

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Lib hiding (step)
open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Operational.TypeStructure

open Category
open Functor
open AlgHom
open Alg
open Signature

Σ⊘ : Signature 
Σ⊘ .Op = ⊥
Σ⊘ .arity ()

module Syntax where

  mutual 
    data VTy : Type  where 
      𝟙 : VTy 
      U : CTy → VTy 

    data CTy : Type  where
      F : VTy → CTy    
      Ans : CTy

  data _⊢v_ : (A A' : VTy) → Type  
  data _⊢c_ : (A : VTy)(B : CTy) → Type  
  data _⊢k_ : (B B' : CTy) → Type  

  data _⊢v_   where
    var : ∀{A}  → A ⊢v A
    tt : ∀{A} → A ⊢v 𝟙
    thunk : ∀{A B} → A ⊢c B → A ⊢v U B

  data _⊢c_ where   
    ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
    bindC : ∀{A A' B} → A ⊢c F A' → A' ⊢c B → A ⊢c B
    force : ∀{A B} →  A ⊢v U B → A ⊢c B    
    yes : ∀{A} → A ⊢c Ans 
    no : ∀{A} → A ⊢c Ans 

  data _⊢k_ where 
    hole : ∀{B} → B ⊢k B
    bindk : ∀{A B B'} → B ⊢k F A → A ⊢c B' → B ⊢k B'

  mutual 
    subV : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subV V var = V
    subV V tt = tt
    subV V (thunk M) = thunk (subC V M)

    subC : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subC V (ret W) = ret (subV V W)
    subC V (bindC M N) = bindC (subC V M) N
    subC V (force W) = force (subV V W)
    subC V yes = yes
    subC V no = no

    plug : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B'
    plug hole M = M
    plug (bindk S M) N = bindC (plug S N) M

    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    kcomp S hole = S
    kcomp S (bindk S' M) = bindk (kcomp S S') M

    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdl var = refl
    subVIdl tt = refl
    subVIdl (thunk M) = cong thunk (subCId M)

    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)
    subVAssoc V W var = refl
    subVAssoc V W tt = refl
    subVAssoc V W (thunk M) = cong thunk (sym (subDist V W M))

    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVIdr V = refl

    subCId : ∀ {A B}(M : A ⊢c B) → subC (var {A}) M ≡ M
    subCId (ret V) = cong ret (subVIdl V)
    subCId (bindC M N) = cong₂ bindC (subCId M) refl
    subCId (force V) = cong force (subVIdl V)
    subCId yes = refl
    subCId no = refl

    kcompIdl : ∀ {B B'} → (M : B ⊢k B') → kcomp (hole {B}) M ≡ M
    kcompIdl hole = refl
    kcompIdl (bindk M x) = cong₂ bindk (kcompIdl M) refl

    kcompIdr : ∀ {B B'} → (M : B ⊢k B') → kcomp M (hole {B'}) ≡ M
    kcompIdr M = refl

    kcompAssoc : ∀ {B₁ B₂ B₃ B₄}(M : B₁ ⊢k B₂)(N : B₂ ⊢k B₃)(P : B₃ ⊢k B₄) → 
      kcomp(kcomp M N) P ≡ kcomp M (kcomp N P)
    kcompAssoc M N hole = refl
    kcompAssoc M N (bindk P x) = cong₂ bindk (kcompAssoc M N P) refl

    plugId : ∀ {A B}(M : A ⊢c B) → plug (hole {B}) M ≡ M
    plugId M = refl

    plugDist : ∀ {A B B' B''}(S : B ⊢k B')(S' : B' ⊢k B'')(M : A ⊢c B) → 
      plug S' (plug S M) ≡ plug (kcomp S S') M
    plugDist S hole M = refl
    plugDist S (bindk S' x) M = cong₂ bindC (plugDist S S' M) refl

    subDist : ∀ {A A' A'' B}(V : A ⊢v A')(V' : A' ⊢v A'')(M : A'' ⊢c B) → 
      subC V (subC V' M) ≡ subC (subV V V') M
    subDist V V' (ret x) = cong ret (sym (subVAssoc V V' x ))
    subDist V V' (bindC M M₁) = cong₂ bindC (subDist V V' M) refl
    subDist V V' (force x) = cong force (sym (subVAssoc V V' x ))
    subDist V V' yes = refl
    subDist V V' no = refl
  
    plugSub : ∀ {A A' B B'}(V : A ⊢v A')(M : A' ⊢c B)(S : B ⊢k B') → 
      subC V (plug S M) ≡ plug S (subC V M)
    plugSub V M hole = refl
    plugSub V M (bindk S x) = cong₂ bindC (plugSub V M S) refl


    -- define CBPVMorphism into transition system model
    -- everything on closed computations 𝟙 ⊢c M : B
    data isTerminal : ∀ {B} → (𝟙 ⊢c B) → Type where 
      yesTerm : isTerminal yes
      noTerm : isTerminal no 
      retTerm : ∀ {A} → (V : 𝟙 ⊢v A) → isTerminal (ret V)

    Terminal : CTy → Type 
    Terminal B = Σ[ M ∈ 𝟙 ⊢c B ] isTerminal M
    
    data isRedex : ∀ {B} → (𝟙 ⊢c B) → Type where 
      forceThunk : ∀ {B}{M : 𝟙 ⊢c B} → isRedex (force (thunk M)) 
      bindRet : ∀ {A B}{V : 𝟙 ⊢v A}{M : A ⊢c B} → isRedex (bindC (ret V) M) 

    Redex : CTy → Type 
    Redex B = Σ[ M ∈ 𝟙 ⊢c B ] isRedex M

    data isRedexAt {B : CTy} : 𝟙 ⊢c B → Type where
      atHole : {trm : 𝟙 ⊢c B} → isRedex trm → isRedexAt trm
      -- the redex is under a bind, the stack is explicitly bindk
      atBind : ∀ {A} {M : 𝟙 ⊢c F A} {N : A ⊢c B}
              → isRedexAt M → isRedexAt (bindC M N)

    RedexInCtx : CTy → Type 
    RedexInCtx B = Σ[ M ∈ 𝟙 ⊢c B ] isRedexAt M

    classify' : ∀{B} → (M : 𝟙 ⊢c B) → isTerminal M ⊎ isRedexAt M 
    classify' (ret V) = inl (retTerm V)
    classify' (bindC (ret V) M) = inr (atHole bindRet) 
    classify' (bindC (bindC M N) P) with (classify' (bindC M N))
    ... | inr M' = inr (atBind {M = (bindC M N)} {P} M')
    classify' (bindC (force M) N) with (classify' (force M)) 
    ... | inr M' = inr (atBind {M = force M}{N} M')
    classify' (force (thunk M)) = inr (atHole forceThunk) 
    classify' yes = inl yesTerm
    classify' no = inl noTerm

    State : CTy → Type 
    State B = Terminal B ⊎ RedexInCtx B 

    extract : {B : CTy} → State B → 𝟙 ⊢c B 
    extract {B} (inl (M , prf)) = M
    extract {B} (inr (M , prf)) = M

    classify : ∀ {B} → 𝟙 ⊢c B → State B
    classify M = map⊎ (λ prf → M , prf) (λ prf → M , prf) (classify' M)

    plug' : {B B' : CTy} → (S : B ⊢k B') → State B → State B' 
    plug' S st = classify (plug S (extract st))

    open import Cubical.Foundations.Isomorphism
    partition : {B : CTy} → Iso (𝟙 ⊢c B) (State B) 
    partition {B} .Iso.fun = classify
    partition {B} .Iso.inv = extract
    partition {B} .Iso.sec = goal where 
      goal : (s : State B) → map⊎ (λ prf → extract s , prf) (λ prf → extract s , prf) (classify' (extract s)) ≡ s
      goal (inl (ret x , retTerm V)) = refl
      goal (inl (yes , yesTerm)) = refl
      goal (inl (no , noTerm)) = refl
      goal (inr (ret x , atHole ()))
      goal (inr (bindC fst₁ fst₂ , atHole bindRet)) = refl
      goal (inr (bindC fst₁ fst₂ , atBind snd₁)) = {! snd₁  !}
      goal (inr (force x , atHole forceThunk)) = refl
      goal (inr (yes , atHole ()))
      goal (inr (no , atHole ()))
    partition {B} .Iso.ret M with (classify' M) 
    ... | inl x = refl
    ... | inr x = refl


    stepRedex : {B : CTy} → Redex B → 𝟙 ⊢c B
    stepRedex (bindC (ret V) M , bindRet) = (subC V M)
    stepRedex (force (thunk M) , forceThunk) = M

    step' : {B : CTy} → RedexInCtx B → 𝟙 ⊢c B
    step' (ret x , atHole ())
    step' (yes , atHole ())
    step' (no , atHole ())
    step' (M , atHole redexM) = stepRedex (M , redexM)
    step' (bindC M N , atBind isRedexAtM) = 
      let M' = step' (M , isRedexAtM) in bindC M' N

    step : {B : CTy} → 𝟙 ⊢c B → 𝟙 ⊢c B
    step M = rec⊎ fst step' (classify M)

    {-
          M ↦ N 
      -------------
       S[M] ↦ S[N]
    -}
    plugHomomorphism : {B : CTy}{M N : 𝟙 ⊢c B} → {!   !}
    plugHomomorphism = {!   !}



module SyntacticModel where 
  open Syntax 

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

  FreeCompAlg : VTy → CTy → Alg Σ⊘
  FreeCompAlg A B .Carrier = A ⊢c B , {!   !}
  FreeCompAlg A B .interp ()
  
  O : Functor (V ^op ×C C) (ALG Σ⊘) 
  O .F-ob (A , B) = FreeCompAlg A B
  O .F-hom (V , S) .carmap M = plug S (subC V M)
  O .F-hom (V , S) .pres ()
  O .F-id = AlgHom≡ (funExt λ M → (plugId (subC var M)) ∙ (subCId M))
  O .F-seq (W , S)(V' , S') = 
    AlgHom≡ (funExt λ M → 
      sym (plugDist S S' (subC (subV V' W) M) ) 
      ∙ cong₂ plug (refl {x = S'}) (sym (plugSub (subV V' W) M S) ∙ sym (subDist V' W (plug S M) ) ∙ cong₂ subC (refl {x = V'}) (plugSub W M S)))

  SynModel : CBPVModel Σ⊘
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

-- https://github.com/um-catlab/cubical-categorical-logic/blob/cbpv-small-step/Cubical/Categories/CBPV/Instances/TransitionSystem.agda
module TransitionSystemModel where 
  open import HyperDoc.Operational.TransitionSystem
  open TSystem

  TSystemModel : CBPVModel Σ⊘
  TSystemModel .CBPVModel.V = SET _
  TSystemModel .CBPVModel.C = TSysCat
  TSystemModel .CBPVModel.O .F-ob (X , S) .Carrier = (SET _) [ X , state S ] , (SET _) .isSetHom
  TSystemModel .CBPVModel.O .F-ob (X , S) .interp ()
  TSystemModel .CBPVModel.O .F-hom {A , B} {A' , B'} (f , h) .carmap g a' = h .TSystem[_,_].s-map (g (f a'))
  TSystemModel .CBPVModel.O .F-hom {A , B} {A' , B'} (f , h) .pres ()
  TSystemModel .CBPVModel.O .F-id = AlgHom≡ refl
  TSystemModel .CBPVModel.O .F-seq _ _ = AlgHom≡ refl

module SynToTSys where 
  open TransitionSystemModel
  open SyntacticModel
  open Syntax hiding (F)
  open import HyperDoc.Operational.TransitionSystem
  open import Cubical.Categories.NaturalTransformation


  module Syn = CBPVModel SynModel

  StateMachine : CTy → ob TSysCat 
  StateMachine B .TSystem.term = (Terminal B) , {!   !}
  StateMachine B .TSystem.redex = (RedexInCtx B) , {!   !}
  StateMachine B .TSystem.red R = classify (step' R)

  -- TODO 
  StateMachineHom : {B B' : CTy} → Syn.C [ B , B' ] → TSysCat [ StateMachine B , StateMachine B' ]
  StateMachineHom S .TSystem[_,_].s-map = plug' S
  StateMachineHom f .TSystem[_,_].lax (inl x) = tt*
  StateMachineHom hole .TSystem[_,_].lax (inr (ret x , atHole ()))
  StateMachineHom hole .TSystem[_,_].lax (inr (bindC fst₁ fst₂ , snd₁)) = {!   !}
  StateMachineHom hole .TSystem[_,_].lax (inr (force (thunk x) , atHole forceThunk)) = {!   !}
  StateMachineHom hole .TSystem[_,_].lax (inr (yes , atHole ()))
  StateMachineHom hole .TSystem[_,_].lax (inr (no , atHole ()))
  StateMachineHom (bindk f x₁) .TSystem[_,_].lax (inr x) = {!   !}

  -- yes.. just annoying to work with StateS instead of closed terms of B
  FC : Functor Syn.C TSysCat
  FC .F-ob = StateMachine 
  FC .F-hom = StateMachineHom
  FC .F-id = TSysMap≡ {!   !}
  FC .F-seq _ _ = TSysMap≡ {!   !}
  
  F : CBPVMorphism SynModel TSystemModel 
  F .CBPVMorphism.FV = Syn.V [ 𝟙 ,-]
  F .CBPVMorphism.FC = FC
  F .CBPVMorphism.FO .NatTrans.N-ob (A , B) .carmap M V = classify (subC V M)
  F .CBPVMorphism.FO .NatTrans.N-ob (A , B) .pres ()
  F .CBPVMorphism.FO .NatTrans.N-hom {(A , B)}{(A' , B')} (V , S) = 
    -- yes, but again annoying to work with as states are not definitionally 𝟙 ⊢c B
    AlgHom≡ (funExt λ M → funExt λ W → {!   !})

module StateMachineLogic where 
  open import HyperDoc.Operational.TransitionSystem
  open TransitionSystemModel
  open import HyperDoc.Logics.SetPred
  open import Cubical.Categories.Instances.Preorders.Monotone
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  open import HyperDoc.Logic.Base
  open import Cubical.Categories.Instances.Posets.Base
  open import Cubical.Relation.Binary.Preorder
  open PreorderStr
  open import Cubical.Foundations.Powerset
  open TSystem
  open TSystem[_,_]
  open import Cubical.Data.Nat
  open import Cubical.Categories.NaturalTransformation


  {-

SubAlg≡ : {Σ : Signature}{A : Alg Σ}→ (P Q : SubAlg A) → (P .fst) ⊃⊂ (Q .fst) →  P ≡ Q
SubAlg≡ {Σ}{A} P Q prf = 
  ΣPathP (funExt (λ a → ⇔toPath (prf .fst a) (prf .snd a)) , 
  toPathP (isPropCong {Σ}{A} (Q .fst) _ _))

    -}


  {-
    in the denotational setting.. 
      - objects of the computation category were algebras 
      - predicates on algebras were closed under the operations of the algebra

    now ..?
      - I don't have any operations atm.. 
      - we discused predicates being closed under antireduction (Jan 15)
        but.. is this sufficient to preserve ops?
  -}

  open CBPVModel TSystemModel
  AntiRedCl : {B : ob C} → ℙ ⟨ state B ⟩ → Type 
  AntiRedCl {B} P = (s t : ⟨ state B ⟩) → ( (_↦*_ B s t ) × ⟨ P t ⟩) → ⟨ P s ⟩

  TSysProp : TSystem _ → Type 
  TSysProp S = Σ[ P ∈ ℙ ⟨ state S ⟩  ] AntiRedCl {S} P

  TSysPo : TSystem ℓ-zero → POSET ℓ-zero ℓ-zero .ob
  TSysPo S .fst .fst = TSysProp S
  TSysPo S .fst .snd .PreorderStr._≤_ P Q = P .fst ⊆ Q .fst
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  TSysPo S .snd = {!   !}

  TSysPropMap : {S T : ob C} → (f : TSystem[ T , S ]) → TSysProp S → TSysProp T
  TSysPropMap f P .fst t = P .fst (f .s-map t)
    -- λ z → P .fst (f .TSystem[_,_].s-map z)
  TSysPropMap f P .snd t t' (( n , t↦*t') , Pft') = P .snd (f .s-map t) (f .s-map t') ((1 , {!   !}) , Pft')

  CH' : Functor (TSysCat ^op) (POSET ℓ-zero ℓ-zero)
  CH' .F-ob = TSysPo
  CH' .F-hom f .MonFun.f = TSysPropMap f
  CH' .F-hom f .MonFun.isMon = λ z x₂ → z (f .s-map x₂)
  CH' .F-id = eqMon _ _ {! refl  !}
  CH' .F-seq = {!   !}

  L : Logic TSystemModel 
  L .Logic.VH = Pred
  L .Logic.CH = CH'
  L .Logic.Sq .NatTrans.N-ob (A , B) f .MonFun.f Q a = Q .fst (f a)
  L .Logic.Sq .NatTrans.N-ob (A , B) f .MonFun.isMon = λ z x₁ → z (f x₁)
  L .Logic.Sq .NatTrans.N-hom {(A , B)}{(A' , B')} (V , S) = {!   !}
  L .Logic.pullOp ()