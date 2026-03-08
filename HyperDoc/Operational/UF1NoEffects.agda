{-# OPTIONS --type-in-type #-}
{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module HyperDoc.Operational.UF1NoEffects where 

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Empty
open import Cubical.Data.Sum renaming (map to map⊎ ; rec to rec⊎) 
open import Cubical.Data.FinData
open import Cubical.HITs.PropositionalTruncation renaming (map to hmap ; rec to hrec)
open import Cubical.Functions.Logic hiding (⊥  ; inl ; inr)

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

  data _⊢c_ where   
    ret : ∀{A A'} → A ⊢v A' → A ⊢c F A'
    bindC : ∀{A A' B} → A ⊢c F A' → A' ⊢c B → A ⊢c B
    force : ∀{A B} →  A ⊢v U B → A ⊢c B    

  data _⊢k_ where 
    hole : ∀{B} → B ⊢k B
    bindk : ∀{A B B'} → B ⊢k F A → A ⊢c B' → B ⊢k B'

  mutual 
    subV : {A A' A'' : VTy} → A ⊢v A' → A' ⊢v A'' → A ⊢v A'' 
    subV V var = V
    subV V tt = tt
    subV V yes = yes
    subV V no = no
    subV V (thunk M) = thunk (subC V M)

    subC : {A A' : VTy}{B : CTy} → A' ⊢v A → A ⊢c B → A' ⊢c B 
    subC V (ret W) = ret (subV V W)
    subC V (bindC M N) = bindC (subC V M) N
    subC V (force W) = force (subV V W)

    plug : {A : VTy}{B B' : CTy} → B ⊢k B' → A ⊢c B → A ⊢c B'
    plug hole M = M
    plug (bindk S M) N = bindC (plug S N) M

    kcomp : ∀ {B B' B''} → B ⊢k B' → B' ⊢k B'' → B ⊢k B'' 
    kcomp S hole = S
    kcomp S (bindk S' M) = bindk (kcomp S S') M

    subVIdl : ∀ {A A'} → (V : A ⊢v A') → subV (var {A}) V ≡ V
    subVIdl var = refl
    subVIdl tt = refl
    subVIdl yes = refl 
    subVIdl no = refl
    subVIdl (thunk M) = cong thunk (subCId M)

    subVAssoc : ∀ {A₁ A₂ A₃ A₄}(V : A₁ ⊢v A₂)(W : A₂ ⊢v A₃)(Y : A₃ ⊢v A₄) → 
      subV (subV V W) Y ≡ subV V (subV W Y)
    subVAssoc V W var = refl
    subVAssoc V W tt = refl
    subVAssoc V W yes = refl
    subVAssoc V W no = refl
    subVAssoc V W (thunk M) = cong thunk (sym (subDist V W M))

    subVIdr : ∀ {A A'} → (V : A ⊢v A') → subV V (var {A'}) ≡ V
    subVIdr V = refl

    subCId : ∀ {A B}(M : A ⊢c B) → subC (var {A}) M ≡ M
    subCId (ret V) = cong ret (subVIdl V)
    subCId (bindC M N) = cong₂ bindC (subCId M) refl
    subCId (force V) = cong force (subVIdl V)


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

  
    plugSub : ∀ {A A' B B'}(V : A ⊢v A')(M : A' ⊢c B)(S : B ⊢k B') → 
      subC V (plug S M) ≡ plug S (subC V M)
    plugSub V M hole = refl
    plugSub V M (bindk S x) = cong₂ bindC (plugSub V M S) refl

    -- define CBPVMorphism into transition system model
    -- everything on closed computations 𝟙 ⊢c M : B
    data isTerminal : ∀ {B} → (𝟙 ⊢c B) → Type where 
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
      goal (inr (ret x , atHole ()))
      goal (inr (bindC fst₁ fst₂ , atHole bindRet)) = refl
      goal (inr (bindC fst₁ fst₂ , atBind snd₁)) = {! snd₁  !}
      goal (inr (force x , atHole forceThunk)) = refl
    partition {B} .Iso.ret M with (classify' M) 
    ... | inl x = refl
    ... | inr x = refl


    stepRedex : {B : CTy} → Redex B → 𝟙 ⊢c B
    stepRedex (bindC (ret V) M , bindRet) = (subC V M)
    stepRedex (force (thunk M) , forceThunk) = M

    step' : {B : CTy} → RedexInCtx B → 𝟙 ⊢c B
    step' (ret x , atHole ())
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

  open TypeStructure TSystemModel

  hasV𝟙 : HasV𝟙 
  hasV𝟙 A .fst = Unit , isSetUnit
  hasV𝟙 A .snd .fst = λ _ → tt
  hasV𝟙 A .snd .snd = λ _ _ → tt

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
  AntiRedCl {B} P = (s t : ⟨ state B ⟩) → ( (_↦*_ B s t ) × (t ∈ P)) → s ∈ P

  isPropRedCl : {B : ob C}{P : ℙ ⟨ state B ⟩} → isProp (AntiRedCl {B} P) 
  isPropRedCl {B}{P} = isPropΠ λ s → isPropΠ λ t → isProp→ (∈-isProp P s)

  TSysProp : TSystem _ → Type 
  TSysProp S = Σ[ P ∈ ℙ ⟨ state S ⟩  ] AntiRedCl {S} P

  TSysProp≡ : {B : ob C}{P Q : TSysProp B} → (P .fst) ⊃⊂ (Q .fst) →  P ≡ Q
  TSysProp≡ {B} {P} {Q} prf = 
    ΣPathP (funExt (λ a → ⇔toPath (prf .fst a) (prf .snd a)) , 
      toPathP (isPropRedCl {B} {Q .fst} _ _))

  TSysPo : TSystem ℓ-zero → POSET ℓ-zero ℓ-zero .ob
  TSysPo S .fst .fst = TSysProp S
  TSysPo S .fst .snd .PreorderStr._≤_ P Q = P .fst ⊆ Q .fst
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-refl P = ⊆-refl (P .fst)
  TSysPo S .fst .snd .isPreorder .IsPreorder.is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
  TSysPo S .snd = {!   !}

  TSysPropMap : {S T : ob C} → (f : TSystem[ T , S ]) → TSysProp S → TSysProp T
  TSysPropMap f P .fst t = P .fst (f .s-map t)
  TSysPropMap f P .snd t t' (( n , t↦*t') , Pft') = 
    -- stepn S n (f .s-map t) ≡ f .s-map (stepn T n t) 
    -- yes this holds via the laxness condition of f applied n many times
    -- deal with this later
    P .snd (f .s-map t) (f .s-map t') ((n , {!   !} ∙ cong (λ h → f .s-map h) t↦*t') , Pft')

  CH' : Functor (TSysCat ^op) (POSET ℓ-zero ℓ-zero)
  CH' .F-ob = TSysPo
  CH' .F-hom f .MonFun.f = TSysPropMap f
  CH' .F-hom f .MonFun.isMon = λ z x₂ → z (f .s-map x₂)
  CH' .F-id = eqMon _ _ (funExt λ P → TSysProp≡ ((λ x z → z) , (λ x z → z)))
  CH' .F-seq _ _ =  eqMon _ _ (funExt λ P → TSysProp≡ ((λ x₁ z₁ → z₁) , (λ x₁ z₁ → z₁)))

  L : Logic TSystemModel 
  L .Logic.VH = Pred
  L .Logic.CH = CH'
  L .Logic.Sq .NatTrans.N-ob (A , B) f .MonFun.f Q a = Q .fst (f a)
  L .Logic.Sq .NatTrans.N-ob (A , B) f .MonFun.isMon = λ z x₁ → z (f x₁)
  L .Logic.Sq .NatTrans.N-hom {(A , B)}{(A' , B')} (V , S) = funExt λ M → eqMon _ _ refl
  L .Logic.pullOp ()

  open import HyperDoc.Logic.Structure
  open import Cubical.Foundations.Isomorphism
  open Iso

  open Push L

  data DirectImage' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ state B ⟩ → Type where 
    base : (b : ⟨ state B ⟩ )(a : ⟨ A ⟩ ) → _↦*_ B b (M a) → a ∈ P → DirectImage' A B M P b

  DirectImage : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → ℙ ⟨ state B ⟩
  DirectImage A B M P b = ∥ DirectImage' A B M P b ∥ₚ

  push' : {A : ob V}{B : ob C} → (M : O'[ A , B ]) →  ℙ ⟨ A ⟩ → TSysProp B
  push' {A} {B} M P .fst = DirectImage A B M P 
  push' {A} {B} M P .snd s t ((n , s↦*t) , t∈DI) = 
    -- yes, just need to prove addition under step
    hmap (λ {(base _ a (m , t↦*Ma) a∈P) → base s a ((n + m) , {!   !}) a∈P}) t∈DI 

  push : {A : ob V}{B : ob C} → (M : O'[ A , B ]) →  MonFun (pred A .fst) (TSysPo B .fst)
  push {A}{B} M .MonFun.f = push' {A}{B} M
  push M .MonFun.isMon {P}{P'} P≤P' s = hmap λ {(base _ a s↦*Ma a∈P) → base s a s↦*Ma (P≤P' a a∈P)}

  hasPush : HasPush
  hasPush M .fst = push M
  hasPush M .snd ._⊣_.adjIff {P}{Q} .fun  M_*P≤Q a a∈P = M_*P≤Q (M a) ∣ (base (M a) a (0 , refl) a∈P) ∣₁
  hasPush M .snd ._⊣_.adjIff {P}{Q} .inv P≤M^*Q s = hrec (∈-isProp (Q .fst) s) λ {(base b a s↦Ma a∈P) → Q .snd s (M a) (s↦Ma , P≤M^*Q a a∈P)} 
  hasPush M .snd ._⊣_.adjIff {P}{Q} .sec b = ⊆-isProp  P (λ x → Q .fst  (M x)) _ b
  hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .ret a = ⊆-isProp  (DirectImage A B M P) (Q .fst) _ a

-- attempt the eliminator, heres where things go arwy 
module Eliminator where 
  open import Cubical.Categories.Displayed.Base
  open import Cubical.Categories.Displayed.Section
  open import HyperDoc.Logic.Base
  open import HyperDoc.Syntax
  open import HyperDoc.Connectives.Connectives
  open import HyperDoc.Logic.Structure
  open import Cubical.Categories.Instances.Preorders.Monotone

  open Syntax
  open SyntacticModel
  open Section
  open Categoryᴰ
  
  record InterpGen 
      (L : Logic (SyntacticModel.SynModel)) : Type where 
    open Logic L
    open Syntax 
    open L⊤.HA 
    private
      module LV = HDSyntax VH 
      module LC = HDSyntax CH 
    field 
      interpAns : LV.F∣ Ans ∣
      interpYes : {A : ob V}{P : LV.F∣ A ∣} → A LV.◂ P ≤ LV.f* yes interpAns
      interpNo : {A : ob V}{P : LV.F∣ A ∣} → A LV.◂ P ≤ LV.f* no interpAns

  module _ ( L : Logic SynModel) where 
    open ConvertLogic SynModel L
    open Logic L
    module LV = HDSyntax VH
    module LC = HDSyntax CH
    open TypeStructure SynModel
    open Push L

    module _ 
      (⊤ : L⊤.Has⊤ VH)
      (V⊤ : HasV𝟙 )
      (push : HasPush)
      (interpGen : InterpGen L) where 
      
      open L⊤.HA 
      open PushSyntax push
      open InterpGen interpGen

      mutual
        vty : (A : VTy) → LV.F∣ A ∣
        vty 𝟙 = top (⊤ .fst 𝟙)
        vty Ans = interpAns
        vty (U B) = pull (force var) $ cty B

        cty : (B : CTy) → LC.F∣ B ∣
        cty (F A) = push (ret var) .fst $ vty A

      mutual 
        vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
        vtm var = Vᴰ .idᴰ
        vtm tt = LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))
        vtm yes = interpYes
        vtm no = interpNo
        {-
          issue : A LV.◂ vty A ≤ LV.f* (thunk M) (pull (force var) $ cty B)
            this is equivalent to 
              (vty A) ≤A (force (thunk M))^* (cty B)
            in the denotational model, we use the β rule to reduce this to 
              (vty A) ≤A M^* (cty B)
            which we have by IH
        -}
        vtm (thunk M) = LV.seq (ctm M) {!   !}
        -- need M^*(cty B) ≤A (force (thunk M))^* (cty B)
   

        ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
        ktm hole = Cᴰ .idᴰ
        ktm (bindk S M) = {!   !}

        ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
        ctm (ret V) = {!   !}
        ctm (bindC M N) = {!   !}
        {-
          this used to be id... 
          when we pulled back by force instead of force var
          now we n.t.s. 

          (force var)^* (cty B) ≤A (force V)^* (cty B)

        -}
        ctm (force V) = LV.seq (vtm V) {!   !}

      SV : Section Id Vᴰ 
      SV .F-obᴰ = vty
      SV .F-homᴰ = vtm
      SV .F-idᴰ = VL.isProp≤  _ _
      SV .F-seqᴰ _ _ = VL.isProp≤  _ _

      SC : Section Id Cᴰ 
      SC .F-obᴰ = cty
      SC .F-homᴰ = ktm
      SC .F-idᴰ = CL.isProp≤  _ _
      SC .F-seqᴰ _ _ = CL.isProp≤  _ _

      M-elim : CBPVGlobalSection L
      M-elim .fst = SV
      M-elim .snd .fst = SC
      M-elim .snd .snd = ctm

{-

      mutual
        vty : (A : VTy) → LV.F∣ A ∣
        vty 𝟙 = top (⊤ .fst 𝟙)
        vty Ans = interpAns
        vty (U B) = pull force $ cty B

        cty : (B : CTy) → LC.F∣ B ∣
        cty (F A) = push ret .fst $  vty A
    
      mutual
        vtm-thunk : ∀ {A  B} → (M : A ⊢c B) →  A LV.◂ vty A ≤ LV.f* (thunk M) (pull force $ cty B) 
        vtm-thunk {A}{B} M = 
          LV.seq (ctm M) (
          LV.eqTo≤ (cong (λ h → MonFun.f (pull h) (cty B)) (sym Uβ ∙ sym plugId)
            ∙ cong (λ h → h .MonFun.f (cty B)) (pullLComp (thunk M) force))) 

        vtm : {A A' : VTy} → (V : A ⊢v A') → A LV.◂ vty A ≤ LV.f* V (vty A')
        vtm var = Vᴰ .idᴰ
        vtm (yes) = interpYes 
        vtm (no) = interpNo  
        vtm (thunk M) = vtm-thunk M
        vtm tt = LV.seq (top-top (⊤ .fst _)) (LV.eqTo≤ (sym (L⊤.HAHom.f-top (⊤ .snd tt))))

        ktm-bind : ∀ {A  B} → (M : A ⊢c B) → F A LC.◂ push ret .fst $ vty A ≤ LC.f* (bind M) (cty B)
        ktm-bind {A}{B} M = 
          pullToPush ret (
            LV.seq (ctm M) (
            LV.eqTo≤ goal)) where 

            goal  : MonFun.f (pull M) (cty B) ≡ pull ret .MonFun.f (LC.f* (bind M) (cty B))
            goal = cong (λ h → N-ob Sq (A , B) h .MonFun.f (cty B)) (sym Fβ ∙ cong₂ plug refl (sym subCId)) 
              ∙  (cong (λ h → h .MonFun.f (cty B))) (pullRComp (bind M) ret)
        

        ktm : {B B' : CTy} → (S : B ⊢k B') → B LC.◂ cty B ≤ LC.f* S (cty B')
        ktm hole = Cᴰ .idᴰ
        ktm (bind M) = ktm-bind M

        ctm : ∀{A B} → (M : A ⊢c B) → A LV.◂ vty A ≤ (pull M $ cty B)
        ctm force = LV.id⊢
        ctm ret = pushToPull ret LC.id⊢

-}
open import HyperDoc.Logic.Base
open import HyperDoc.Connectives.Connectives
open import HyperDoc.Logic.Structure
open import HyperDoc.Syntax
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Constructions.Reindex.Base renaming (reindex to reindexᴰ)

open NatTrans
open Section


module LocalElim
  (N : CBPVModel Σ⊘)
  (L : Logic N)
  (⊤ : L⊤.Has⊤ (Logic.VH L))
  (V⊤ : TypeStructure.HasV𝟙 N)
  (push : Push.HasPush L)  where 

  open Syntax
  open SyntacticModel

  module _ (F : CBPVMorphism SynModel N) where
    open Reindex F L 
    open ModelSection
    open CBPVMorphism F
    open TypeStructure
    open ConvertLogic N L

    LM : Logic SynModel
    LM = reindex

    open Eliminator
    open Push

    module LMHV = HDSyntax (Logic.VH LM)
    module LMHC = HDSyntax (Logic.CH LM)

    pres⊤ : L⊤.Has⊤ (Logic.VH LM) 
    pres⊤ .fst = λ c → ⊤ .fst (F-ob (FV ^opF) c)
    pres⊤ .snd = λ f → ⊤ .snd (F-hom (FV ^opF) f)

    presPush : HasPush LM
    presPush M = 
      (push (N-ob FO (_ , _) .carmap M) .fst) ,
        push (N-ob FO (_ , _) .carmap M) .snd

    module _ (interp : InterpGen LM) where
      M-elim' : CBPVGlobalSection LM
      M-elim' = M-elim LM pres⊤ hasV𝟙 presPush interp

      FSV : Section FV Vᴰ
      FSV = GlobalSectionReindex→Section Vᴰ FV convert where 
        convert : GlobalSection (reindexᴰ Vᴰ FV)
        convert .Section.F-obᴰ = M-elim' .fst .Section.F-obᴰ
        convert .Section.F-homᴰ = M-elim' .fst .Section.F-homᴰ
        convert .Section.F-idᴰ = LMHV.isProp≤ _ _
        convert .Section.F-seqᴰ _ _ = LMHV.isProp≤ _ _
      
      FSC : Section FC Cᴰ 
      FSC = GlobalSectionReindex→Section Cᴰ FC convert where 
        convert : GlobalSection (reindexᴰ Cᴰ FC)
        convert .Section.F-obᴰ = M-elim' .snd .fst .Section.F-obᴰ
        convert .Section.F-homᴰ = M-elim' .snd .fst .Section.F-homᴰ
        convert .Section.F-idᴰ = LMHC.isProp≤ _ _
        convert .Section.F-seqᴰ _ _ = LMHC.isProp≤ _ _ 
      
      M-elim-local : CBPVSection F L 
      M-elim-local .fst = FSV
      M-elim-local .snd .fst = FSC
      M-elim-local .snd .snd = M-elim' .snd .snd

module Example where 
  open TransitionSystemModel
  open StateMachineLogic
  open import HyperDoc.Logics.SetPred
  open ModelSection
  open SynToTSys renaming (F to GL)
  open Eliminator
  open InterpGen
  open import Cubical.Foundations.Powerset
  open import Cubical.Categories.Instances.Preorders.Monotone
  open MonFun
  open import HyperDoc.Operational.TransitionSystem

  open LocalElim TSystemModel L has⊤ hasV𝟙 hasPush
  
  open Syntax

  property : 𝟙 ⊢v Ans → hProp _ 
  property V = ∥ (V ≡ yes) ⊎ (V ≡ no) ∥ₚ

  int : InterpGen (LM GL)
  int .interpAns = property
  int .interpYes V x∈P = ∣ (inl refl) ∣₁
  int .interpNo V x∈P = ∣ (inr refl) ∣₁

  LR : CBPVSection GL L 
  LR = M-elim-local GL int


  open TSystem (StateMachine (F Ans))
  -- this notion of transition machine sucks to work with "on this side"
  -- its nicer for the maps into delay.. which we don't care about.. 
  retYes : ⟨ state ⟩ 
  retYes = inl ((ret (subV var yes)) , retTerm (subV var yes))

  retNo : ⟨ state ⟩ 
  retNo = inl ((ret (subV var no)) , retTerm (subV var no))

  theorem :  (M : 𝟙 ⊢c F Ans) → ∥ (classify M ↦* retYes) ⊎ (classify M ↦* retNo) ∥₁
  theorem M = {! var ∈
      f (Logic.pull L (N-ob (CBPVMorphism.FO GL) (𝟙 , F A) .carmap M))
      (F-obᴰ (LR .snd .fst) (F A))!} where 
    have : M ∈ {!   !}
    have = LR .snd .snd M var tt*



    {-

    ∥
DirectImage' ((𝟙 ⊢v A) , ?3) (StateMachine (F A))
(λ V → inl (ret V , retTerm V))
(vty (Reindex.reindex GL L) (pres⊤ GL) SyntacticModel.hasV𝟙
 (λ M₁ →
    hasPush
    (λ V →
       map⊎ (λ prf → subC V M₁ , prf) (λ prf → subC V M₁ , prf)
       (classify' (subC V M₁))))
 int A)
(map⊎ (λ prf → subC var M , prf) (λ prf → subC var M , prf)
 (classify' (subC var M)))
∥₁
      -}