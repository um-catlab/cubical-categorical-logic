{-# OPTIONS --type-in-type #-}
module HyperDoc.Operational.Effects.Instances where 

open import Cubical.Data.Sigma

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation

open import HyperDoc.Operational.Effects.Model 
open import HyperDoc.Operational.Effects.AlgGraph
open import HyperDoc.Operational.Effects.Syntax
open import HyperDoc.Algebra.Algebra
open import HyperDoc.Operational.Graph

open BifunctorSep
open BifunctorSepᴰ
open Category
open Categoryᴰ
open Functor
open NatTrans
open AlgGraph
open AlgPre

open import Cubical.Categories.Instances.Preorders.Base
open import Cubical.Categories.Instances.Preorders.Monotone
open import Cubical.Relation.Binary.Preorder renaming (Preorder to Preorder')
open MonFun renaming (f to fun)
open PreorderStr
open  IsPreorder



module _ (Sig : Signature) where 

  aPre : hSet ℓ-zero → AlgPre Sig → AlgGraph Sig
  aPre X P .fst = (⟨ X ⟩ → P .fst .fst .fst) , isSet→ (P .fst .snd)
  aPre X P .snd .fst f g = (((x : ⟨ X ⟩ ) → P .fst .fst .snd ._≤_  (f x) (g x))) , (isSetΠ λ x → isProp→isSet (P .fst .fst .snd .isPreorder .is-prop-valued (f x) (g x)))
  aPre X P .snd .snd op args f = P .snd op (λ z → args z f)

  aPre-homL : {X Y : hSet _ } → ((SET _) ^op) [ X , Y ] → (P : AlgPre Sig) → ALGGRAPH Sig [ aPre X P , aPre Y P ]
  aPre-homL {X} {Y} f P .fst = λ z z₁ → z (f z₁)
  aPre-homL {X} {Y} f P .snd .fst = λ z x → z (f x)
  aPre-homL {X} {Y} f P .snd .snd op args = refl

  aPre-homR : {P Q  : AlgPre Sig} → (X : hSet _) → (ALGPRE Sig) [ P , Q ] → ALGGRAPH Sig  [ aPre X P , aPre X Q ]
  aPre-homR X h .fst = λ z z₁ → h .fst .fun (z z₁)
  aPre-homR X h .snd .fst = λ z x → h .fst .isMon (z x)
  aPre-homR X h .snd .snd op args = funExt λ x → h .snd op (λ z → args z x)

  Sem : CBPVModel Sig
  Sem .fst = SET _
  Sem .snd .fst = ALGPRE Sig
  Sem .snd .snd .Bif-ob = aPre
  Sem .snd .snd .Bif-homL {X}{Y}  = aPre-homL {X}{Y} 
  Sem .snd .snd .Bif-L-id = refl
  Sem .snd .snd .Bif-L-seq _ _ = ΣPathP (refl , ΣPathP (refl , {! refl  !}))
  Sem .snd .snd .Bif-homR {P}{Q} = aPre-homR {P}{Q}
  Sem .snd .snd .Bif-R-id = refl
  Sem .snd .snd .Bif-R-seq _ _ = ΣPathP (refl , ΣPathP (refl , {! refl  !}))
  Sem .snd .snd .SepBif-RL-commute _ _ = ΣPathP (refl , ΣPathP (refl , {! refl  !}))

  module SynMod =  SynModel Sig
  module Syn =  Syntax Sig 
  CL : CBPVMorphism SynMod.Syn Sem 
  CL .fst = SynMod.V [ Syn.𝟙 ,-]
  CL .snd .fst = RTC.RTCAlgGraphF Sig ∘F appL (mkBifunctorSep SynMod.O) Syn.𝟙
  CL .snd .snd .N-ob (A , B) .fst M V = Syn.subC V  M
  CL .snd .snd .N-ob (A , B) .snd .fst {M}{M'} M↦M' V = tran (Syn.subC-cong M↦M') ref
  CL .snd .snd .N-ob (A , B) .snd .snd op args = funExt λ V → Syn.opsSub V op args
  CL .snd .snd .N-hom (V , S) = {!   !} 

  open import HyperDoc.Operational.Effects.Logic
  open import HyperDoc.Logics.SetPred  
  open import Cubical.Categories.Instances.Posets.Base
  open import Cubical.Foundations.Powerset 
  open import HyperDoc.Lib 
  open import Cubical.Functions.Logic 
  open import Cubical.HITs.PropositionalTruncation renaming (map to hmap ; rec to hrec)
  open import Cubical.Categories.Instances.Preorders.Monotone.Adjoint
  open import Cubical.Foundations.Isomorphism
  open Iso

  AntiRedAlgCl : {B : AlgPre Sig} → ℙ ⟨ B .fst .fst ⟩ → Type 
  AntiRedAlgCl {B} P = {!   !}

  ALPred : AlgPre Sig → Type 
  ALPred B = Σ[ P ∈ ℙ ⟨ B .fst .fst ⟩ ] {!   !}

  apro : AlgPre Sig → POSET _ _  .ob 
  apro B .fst .fst = ALPred B
  apro B .fst .snd = {!   !}
  apro B .snd = {!   !}

  LC : Functor (ALGPRE Sig ^op) (POSET _ _ ) 
  LC .F-ob = apro
  LC .F-hom = {!   !}
  LC .F-id = {!   !}
  LC .F-seq = {!   !}

  SemLog : CBPVLogic Sem 
  SemLog .CBPVLogic.LV = Pred
  SemLog .CBPVLogic.LC = LC
  SemLog .CBPVLogic.LSq = {!   !}
  SemLog .CBPVLogic.antired = {!   !}
  SemLog .CBPVLogic.pullOp = {!   !}

  open CBPVModelSyntax Sem

  -- can this be closed under the algebra and antireduction?
  data DirectImageCong' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : B .fst .fst .fst  → Type where 
    base : (b : B .fst .fst .fst )(a : ⟨ A ⟩ ) → {!   !} →  a ∈ P → DirectImageCong' A B M P b
    -- M a ≡ b → a ∈ P → DirectImageCong' A B M P b
    

{-


    AntiRedCl : {B : Preorder} → ℙ (B .fst .fst) → Type 
    AntiRedCl {B} P = (x y : B .fst .fst) → B .fst .snd ._≤_ x y × (y ∈ P) → x ∈ P


    data DirectImageCong' (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) : ⟨ B .Carrier ⟩ → Type where 
      base : (b : ⟨ B .Carrier ⟩ )(a : ⟨ A ⟩ ) → M a ≡ b → a ∈ P → DirectImageCong' A B M P b
      step : 
            (op : Op)
            (args : Fin (arity op) → ⟨ B .Carrier ⟩ )
            (dargs : (a : Fin (arity op)) → DirectImageCong' A B M P (args a) ) → 
            DirectImageCong' A B M P (B .interp op args)

    DICong-elim : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → 
      (motive : ∀ (b : ⟨ B. Carrier ⟩) → DirectImageCong' A B M P b  → Type)
      (base-case : 
        (b : ⟨ B .Carrier ⟩) 
        (a : ⟨ A ⟩ ) 
        (eq : M a ≡ b)
        (a∈P : a ∈ P) → 
        motive b (base b a eq a∈P ))
      (step-case : 
        (op : Op)
        (args : Fin (arity op) → ⟨ B .Carrier ⟩)
        (dargs : (a : Fin (arity op)) → DirectImageCong' A B M P (args a)) 
        (motives : (a : Fin (arity op)) → motive (args a) (dargs a) ) → 
        motive (B .interp op args) (step op args dargs)) 

      → (b : ⟨ B .Carrier ⟩) → (C : DirectImageCong' A B M P b) → motive b C  
    DICong-elim A B M P mot bc sc b (base b₁ a eq prf) = 
      bc b a eq prf
    DICong-elim A B M P mot bc sc b (step op args dargs) = 
      sc op args dargs λ a → DICong-elim A B M P mot bc sc (args a) (dargs a)


    DirectImageCong : (A : V .ob)(B : C .ob)(M : O'[ A , B ])(P : ℙ ⟨ A ⟩) → ℙ ⟨ B .Carrier ⟩
    DirectImageCong A B M P b = ∥ DirectImageCong' A B M P b ∥ₚ

    push' : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      ℙ ⟨ A ⟩ → SubAlg B
    push' {A} {B} M P .fst = DirectImageCong A B M P
    push' {A} {B} M P .snd op args = goal where 

      b' : ⟨ B .Carrier ⟩  
      b' = interp B op (λ a → args a .fst)

      goal : b' ∈ (DirectImageCong A B M P)
      goal = 
        recFin 
          {m = arity op} 
          squash₁ 
          (λ x → ∣ (step op (λ a → args a .fst) x) ∣₁) 
          (λ a → args a .snd)


    push : {A : V .ob}{B : C .ob}→ 
      (M : O'[ A , B ]) →  
      MonFun (pred A .fst) (subAlgPo B .fst) 
    push {A} {B} M .MonFun.f = push' {A}{B} M
    push {A} {B} M .MonFun.isMon {P}{Q} P≤Q b = map goal where 
      goal : DirectImageCong' A B M P b → DirectImageCong' A B M Q b
      goal = 
        DICong-elim A B M P 
          (λ b _  → DirectImageCong' A B M Q b) 
          (λ b₁ a eq a∈P → base b₁ a eq (P≤Q a a∈P)) 
          (λ op args dargs → step op args) 
          b

    hasPush : HasPush
    hasPush M .fst = push M
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .fun = goal where 
      goal : 
        ((b : fst (Carrier B)) →
        ∥ DirectImageCong' A B M P b ∥₁ → b ∈ (Q .fst)) →
        (a : fst A) → a ∈ P  → (M a) ∈ (Q .fst)
      goal trans a Pa = trans (M a) ∣ (base (M a) a refl Pa) ∣₁

    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q}  .inv = goal where 
      goal : 
        ((a : fst A) → a ∈ P → (M a) ∈ (Q .fst)) →
        (b : fst (Carrier B)) → ∥ DirectImageCong' A B M P b ∥₁ → b ∈ (Q .fst)
      goal tran b = 
        rec 
          (∈-isProp (λ z → z) (Q .fst b)) 
          (DICong-elim A B M P 
            (λ b _ → b ∈ (Q .fst)) 
            (λ b a eq a∈P → subst (λ h → h ∈ (Q .fst)) eq (tran a a∈P)) 
            (λ op args dargs mot → Q .snd op (λ z → args z , mot z)) 
            b)
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .sec b = ⊆-isProp P (λ x → Q .fst  (M x)) _ b
    hasPush {A}{B} M .snd ._⊣_.adjIff {P}{Q} .Iso.ret a = ⊆-isProp (DirectImageCong A B M P) (Q .fst) _ a


AntiRedCl : {B : Preorder} → ℙ (B .fst .fst) → Type 
AntiRedCl {B} P = (x y : B .fst .fst) → B .fst .snd ._≤_ x y × (y ∈ P) → x ∈ P

isPropRedCl : {B : Preorder}{P : ℙ ⟨ B .fst ⟩} → isProp (AntiRedCl {B} P) 
isPropRedCl {B}{P} = isPropΠ λ s → isPropΠ λ t → isProp→ (∈-isProp P s)

ARPred : Preorder → Type 
ARPred B = Σ[ P ∈ ℙ ⟨ B .fst ⟩ ] AntiRedCl {B} P

ARPred≡ : {B : Preorder}{P Q : ARPred B} → (P .fst) ⊃⊂ (Q .fst) →  P ≡ Q
ARPred≡ {B} {P} {Q} prf = 
  ΣPathP (funExt (λ a → ⇔toPath (prf .fst a) (prf .snd a)) , 
    toPathP (isPropRedCl {B} {Q .fst} _ _))

ARPo : Preorder → ob (POSET _ _ ) 
ARPo B .fst .fst = ARPred B
ARPo B .fst .snd ._≤_ P Q = P .fst ⊆ Q .fst
ARPo B .fst .snd .isPreorder .is-prop-valued P Q = ⊆-isProp (P .fst)(Q .fst)
ARPo B .fst .snd .isPreorder .is-refl P = ⊆-refl (P .fst)
ARPo B .fst .snd .isPreorder .is-trans P Q R = ⊆-trans (P .fst) (Q .fst) (R .fst)
ARPo B .snd = {!   !} 

ARPoMon : {B B' : Preorder} → MonFun (B' .fst) (B .fst) → MonFun (ARPo B .fst) (ARPo B' .fst)
ARPoMon {B} {B'} f .fun P .fst = λ z → P .fst (f .fun z)
ARPoMon {B} {B'} f .fun P .snd = λ x y z → P .snd (f .fun x) (f .fun y) (f .isMon (z .fst) , z .snd)
ARPoMon {B} {B'} f .isMon = λ z x₁ → z (f .fun x₁)

LC : Functor (CBPVModelSyntax.C Sem ^op) (POSET _ _ ) 
LC .F-ob = ARPo
LC .F-hom = ARPoMon
LC .F-id = eqMon _ _ refl
LC .F-seq _ _ = eqMon _ _ refl

SemLog : CBPVLogic Sem 
SemLog .CBPVLogic.LV = Pred
SemLog .CBPVLogic.LC = LC
SemLog .CBPVLogic.LSq .N-ob (A , B) f .fun (g , gcl) a = g (f a)
SemLog .CBPVLogic.LSq .N-ob (A , B) f .isMon = λ z x₁ → z (f x₁)
SemLog .CBPVLogic.LSq .N-hom f = funExt λ g → eqMon _ _ refl 
SemLog .CBPVLogic.antired {A}{B}{Q}{M}{M'} f a QM'a = Q .snd (M a) (M' a) (f a , QM'a)



open LogicStruct SemLog 
has𝟙ᴸ : Has𝟙ᴸ 
has𝟙ᴸ = has⊤

has×ᴸ : Has×ᴸ
has×ᴸ .fst = has∧
{-

open LogicStruct L 

-- Q: why is all the type structure trivial ? 
-- is it because we are actually mapping into universal properties and should expect Isomorphisms?

has𝟙ᴸ : Has𝟙ᴸ 
has𝟙ᴸ = has⊤

has×ᴸ : Has×ᴸ
has×ᴸ .fst = has∧
has×ᴸ .snd = has∃

has+ᴸ : Has+ᴸ semHas+
has+ᴸ .fst = has∨
has+ᴸ .snd .fst = has∃
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-1 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-2 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-1 = λ φ ψ → tt
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-2 = λ φ ψ → tt

hasUTyᴸ : HasUTyᴸ semHasUTy 
hasUTyᴸ .fst = λ x z → z
hasUTyᴸ .snd = λ φ ψ → tt

hasFTyᴸ : HasFTyᴸ semHasFTy
hasFTyᴸ .fst f .fst = {!   !}
hasFTyᴸ .fst f .snd = {!   !}
hasFTyᴸ .snd .fst = λ x z → z
hasFTyᴸ .snd .snd = λ φ ψ → tt

SemLog : CBPVLogic Sem 
SemLog .CBPVLogic.LV = {!   !}
SemLog .CBPVLogic.LC = {!   !}
SemLog .CBPVLogic.LSq = {!   !}
SemLog .CBPVLogic.antired = {!   !}



-}

{-

CL : CBPVMorphism Syn Sem 
CL .fst = V [ 𝟙 ,-]
CL .snd .fst = appL (mkBifunctorSep O) 𝟙
CL .snd .snd .N-ob (A , B) .fst M V = subC V M
CL .snd .snd .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M'
CL .snd .snd .N-hom (V , S) = ΣPathP ((funExt (λ M → funExt λ V' → plugSub ∙ cong₂ plug refl subDist)) , 
  toPathP (implicitFunExt (implicitFunExt (funExt λ _ → funExt λ V' → isProp↦ _ _))) ) 
-}



{-
-- functions and pointwise relations
Gr : hSet _ → Graph _ _ → Graph _ _  
Gr A (N , E) .fst = (⟨ A ⟩ → ⟨ N ⟩) , isSet→ (N .snd)
Gr A (N , E) .snd f g = ((a : ⟨ A ⟩) → ⟨ E (f a) (g a) ⟩) , isSetΠ λ _ → E (f _) (g _) .snd

Gr-homL : {X Y : hSet _ }→ (SET _) [ X , Y ] → (G : Graph _ _ ) → (GRAPH _ _ ) [ Gr Y G , Gr X G ]
Gr-homL {X} {Y} f G .fst h x = h (f x)
Gr-homL {X} {Y} f G .snd h x = h (f x)

Gr-homR : {G G' : Graph _ _ } → 
  (A : hSet ℓ-zero) → GRAPH ℓ-zero ℓ-zero [ G , G' ] → GRAPH ℓ-zero ℓ-zero [ Gr A G , Gr A G' ]
Gr-homR {G} {G'} A G'' .fst f a = G'' .fst (f a)
Gr-homR {G} {G'} A G'' .snd f a = G'' .snd (f a)

Sem : CBPVModel _ _ _ _ _ _ 
Sem .fst = SET _
Sem .snd .fst = GRAPH _ _
Sem .snd .snd .Bif-ob = Gr
Sem .snd .snd .Bif-homL {X}{Y} = Gr-homL {Y}{X}
Sem .snd .snd .Bif-L-id = refl
Sem .snd .snd .Bif-L-seq _ _ = refl
Sem .snd .snd .Bif-homR {G}{G'} = Gr-homR {G}{G'}
Sem .snd .snd .Bif-R-id = refl
Sem .snd .snd .Bif-R-seq _ _ = refl
Sem .snd .snd .SepBif-RL-commute _ _ = refl

rGr : hSet _ → RGraph _ _ → RGraph _ _  
rGr A ((N , E), rid) .fst .fst = (⟨ A ⟩ → ⟨ N ⟩) , isSet→ (N .snd)
rGr A ((N , E), rid) .fst .snd f g = ((a : ⟨ A ⟩) → ⟨ E (f a) (g a) ⟩) , isSetΠ λ _ → E (f _) (g _) .snd
rGr A ((N , E), rid) .snd f a = rid (f a)



open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Empty
open import HyperDoc.Operational.TypeStructure
open TypeStructure Sem 
open Has+'
open WkRepresentation

semHas𝟙 : Has𝟙 
semHas𝟙 .fst = Unit , isSetUnit
semHas𝟙 .snd .N-ob = λ x _ _ → tt
semHas𝟙 .snd .N-hom _ = refl

semHas× : Has× 
semHas× A A' .fst = (⟨ A ⟩ × ⟨ A' ⟩) , (isSet× (A .snd) (A' .snd))
semHas× A A' .snd .N-ob A'' (f , g) a'' = f a'' , g a''
semHas× A A' .snd .N-hom _ = refl

semHas+ : Has+ 
semHas+ A A' .A+A' = (⟨ A ⟩ ⊎ ⟨ A' ⟩) , isSet⊎ (A .snd) (A' .snd)
semHas+ A A' .Has+'.match .N-ob G (f , g) (inl x) = f x
semHas+ A A' .Has+'.match .N-ob G (f , g) (inr x) = g x
semHas+ A A' .Has+'.match .N-hom h i fg (inl x) = h .fst (fg .fst x)
semHas+ A A' .Has+'.match .N-hom h i fg (inr x) = h .fst (fg .snd x)
semHas+ A A' .Has+'.σ₁ = inl
-- f a = f (inl a)
semHas+ A A' .Has+'.σ₂ = inr
-- f a' = f (inr a')
-- need at least reflexive closure of a graph
semHas+ A A' .Has+'.+β₁ M M' a = {!   !} -- ⟨ B .snd (M a) (M a) ⟩
semHas+ A A' .Has+'.+β₂ M M' a' = {!   !} --⟨ B .snd (M' a') (M' a') ⟩

semHasUTy : HasUTy 
semHasUTy G .rep = G .fst
semHasUTy G .fwd .N-ob A f = f
semHasUTy G .fwd .N-hom _ = refl
semHasUTy G .bkwd f = f
semHasUTy G .wkretract {A} f a = {!   !} -- ⟨ G .snd (f a) (f a) ⟩

semHasFTy : HasFTy 
semHasFTy A .rep = A , λ a a' → ⊥ , λ()
semHasFTy A .fwd .N-ob G = fst
semHasFTy A .fwd .N-hom _ = refl
semHasFTy A .bkwd f = f , λ ()
semHasFTy A .wkretract {G} f a = {!   !} -- ⟨ G .snd (f a) (f a) ⟩

CL : CBPVMorphism Syn Sem 
CL .fst = V [ 𝟙 ,-]
CL .snd .fst = appL (mkBifunctorSep O) 𝟙
CL .snd .snd .N-ob (A , B) .fst M V = subC V M
CL .snd .snd .N-ob (A , B) .snd {M}{M'} M↦M' V = subC-cong M↦M'
CL .snd .snd .N-hom (V , S) = ΣPathP ((funExt (λ M → funExt λ V' → plugSub ∙ cong₂ plug refl subDist)) , 
  toPathP (implicitFunExt (implicitFunExt (funExt λ _ → funExt λ V' → isProp↦ _ _))) ) 
  
Grᴰ : {A : hSet _}{G : Graph _ _ } → 
  (SETᴰ _ _ .ob[_] A) → (Graphᴰ _ _ G) → Graphᴰ _ _  (Gr A G)
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .fst n = ((a : ⟨ A ⟩) → ⟨ Aᴰ a ⟩ → ⟨ Nᴰ (n a) ⟩) , isSetΠ2 λ x y → Nᴰ (n x) .snd
Grᴰ {A} {G} Aᴰ (Nᴰ , Eᴰ) .snd {n}{n'} n↦n' nᴰ n'ᴰ = 
  ({ a a' : ⟨ A ⟩}(aᴰ : ⟨ Aᴰ a ⟩)(a'ᴰ : ⟨ Aᴰ a ⟩)→ ⟨ Eᴰ (n↦n' a) (nᴰ a aᴰ) (n'ᴰ a a'ᴰ) ⟩) , 
  isSetImplicitΠ2 λ _ _ → isSetΠ2 λ _ _ → Eᴰ (n↦n' _) (nᴰ _ _) (n'ᴰ _ _) .snd



open import Cubical.Categories.Instances.Preorders.Monotone

open import HyperDoc.Operational.Logic
open import HyperDoc.Logics.SetPred  
open import Cubical.Categories.Instances.Posets.Base

Hmm : Functor ((GRAPH _ _) ^op) (POSET _ _) 
Hmm .F-ob G = pred (G .fst)
Hmm .F-hom = λ z →
    record
    { f = λ z₁ z₂ → fst (z₁ (z .fst z₂)) , z₁ (z .fst z₂) .snd
    ; isMon = λ {x = x₁} {y = y₁} z₁ x₂ → z₁ (z .fst x₂)
    }
Hmm .F-id = eqMon _ _ refl
Hmm .F-seq f g = eqMon _ _ refl

-- anti reduction closed ?
L : CBPVLogic Sem 
L .CBPVLogic.LV = Pred
L .CBPVLogic.LC = Hmm
L .CBPVLogic.LSq .N-ob (A , G) f = record
  { f = λ z z₁ → fst (z (f z₁)) , z (f z₁) .snd
  ; isMon = λ {x} {y} z x₁ → z (f x₁)
  }
L .CBPVLogic.LSq .N-hom (f , h )= funExt λ g → eqMon _ _  refl
--L .CBPVLogic.LRel f g h = Unit , isPropUnit
L .CBPVLogic.RelLComp = λ e _ → tt
L .CBPVLogic.RelRComp = λ e _ → tt

open LogicStruct L 

-- Q: why is all the type structure trivial ? 
-- is it because we are actually mapping into universal properties and should expect Isomorphisms?

has𝟙ᴸ : Has𝟙ᴸ 
has𝟙ᴸ = has⊤

has×ᴸ : Has×ᴸ
has×ᴸ .fst = has∧
has×ᴸ .snd = has∃

has+ᴸ : Has+ᴸ semHas+
has+ᴸ .fst = has∨
has+ᴸ .snd .fst = has∃
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-1 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.anti-2 = λ x z → z
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-1 = λ φ ψ → tt
has+ᴸ .snd .snd .LogicStruct.Has+ᴸ'.edge-2 = λ φ ψ → tt

hasUTyᴸ : HasUTyᴸ semHasUTy 
hasUTyᴸ .fst = λ x z → z
hasUTyᴸ .snd = λ φ ψ → tt

hasFTyᴸ : HasFTyᴸ semHasFTy
hasFTyᴸ .fst f .fst = {!   !}
hasFTyᴸ .fst f .snd = {!   !}
hasFTyᴸ .snd .fst = λ x z → z
hasFTyᴸ .snd .snd = λ φ ψ → tt


Semᴰ : CBPVModelᴰ Sem _ _ _ _ _ _
Semᴰ .fst = SETᴰ _ _
Semᴰ .snd .fst = GRAPHᴰ _ _ _ _
Semᴰ .snd .snd .Bif-obᴰ {A}{G} = Grᴰ {A}{G}
Semᴰ .snd .snd .Bif-homLᴰ {A} {A'} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .fst h hᴰ a' a'ᴰ = hᴰ (f a') (fᴰ a' a'ᴰ)
Semᴰ .snd .snd .Bif-homLᴰ {A} {A'} {f} {Aᴰ} {A'ᴰ} fᴰ {G} Gᴰ .snd {h}{h'}{e} hᴰ h'ᴰ z {a} {a'} aᴰ a'ᴰ = 
  z {f a}{f a'} (fᴰ a aᴰ) (fᴰ a a'ᴰ)
Semᴰ .snd .snd .Bif-L-idᴰ = refl
Semᴰ .snd .snd .Bif-L-seqᴰ _ _ = refl
Semᴰ .snd .snd .Bif-homRᴰ {G} {G'} {h} {Gᴰ} {Gᴰ'} hᴰ {A} Aᴰ .fst n nᵈ a aᴰ = hᴰ .fst (n a) (nᵈ a aᴰ)
Semᴰ .snd .snd .Bif-homRᴰ {G} {G'} {h} {Gᴰ} {Gᴰ'} hᴰ {A} Aᴰ .snd {n}{nᵈ}{e} nᴰ n'ᴰ eᴰ {a}{a'} aᴰ aᴰ' = 
  hᴰ .snd  (nᴰ a aᴰ) (n'ᴰ a aᴰ') (eᴰ {a}{a'} aᴰ aᴰ')
Semᴰ .snd .snd .Bif-R-idᴰ = refl
Semᴰ .snd .snd .Bif-R-seqᴰ _ _ = refl
Semᴰ .snd .snd .SepBif-RL-commuteᴰ _ _ = refl

-}
has×ᴸ .snd = has∃

has+ᴸ : Has+ᴸ 
has+ᴸ .fst = has∨
has+ᴸ .snd = has∃


module Sem =  CBPVModelSyntax Sem

data FreeARPred' (A : Sem.V .ob)(B : Sem.C .ob)(M : Sem.O'[ A , B ])(P : ℙ ⟨ A ⟩)  : ⟨ B .fst ⟩ → Type where 
  free : (b : ⟨ B .fst ⟩)(a : ⟨ A ⟩) →  B .fst .snd ._≤_ b (M a)  → a ∈ P → FreeARPred'  A B M P b 


FreeARPred : (A : Sem.V .ob)(B : Sem.C .ob)(M : Sem.O'[ A , B ])(P : ℙ ⟨ A ⟩) → ARPred B
FreeARPred A B M P .fst b = ∥ FreeARPred' A B M P b ∥ₚ
FreeARPred A B M P .snd b b' (b≤b' , b'∈Free )= 
  hmap (λ {(free _ a b'≤Ma a∈P) → free b a (is-trans (isPreorder (B .fst .snd)) b b' (M a) b≤b' b'≤Ma) a∈P}) b'∈Free

hasFTyᴸ : HasFTyᴸ 
hasFTyᴸ {A} {B} M .fst .fun = FreeARPred A B M
hasFTyᴸ {A} {B} M .fst .isMon {P}{P'} P≤P' b = hmap λ {(free _ a b≤Ma a∈P) → free b a b≤Ma (P≤P' a a∈P)}
hasFTyᴸ {A} {B} M .snd ._⊣_.adjIff {P}{Q} .fun M_P≤Q a a∈P = M_P≤Q (M a)
  ∣ free (M a) a (is-refl (isPreorder (B .fst .snd)) (M a)) a∈P ∣₁
hasFTyᴸ {A} {B} M .snd ._⊣_.adjIff {P}{Q} .inv P≤M*Q b = hrec (∈-isProp (Q .fst) b) λ {(free _ a b≤Ma a∈P) → Q .snd b (M a) (b≤Ma , P≤M*Q a a∈P)}
hasFTyᴸ {A} {B} M .snd ._⊣_.adjIff {P}{Q} .sec f = ⊆-isProp  P (λ x → Q .fst  (M x)) _ f
hasFTyᴸ {A} {B} M .snd ._⊣_.adjIff {P}{Q} .Iso.ret f = ⊆-isProp  (λ b → ∥ FreeARPred' A B M P b ∥ₚ) (Q .fst) _ f



-}