{-# OPTIONS --type-in-type #-}
-- fix level issues
-- reorder imports, etc
module HyperDoc.CBPV.TypeStructure where

open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.FunctorComprehension.Base 
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Profunctor.General 
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Instances.Sets

open import HyperDoc.Algebra.Algebra
open import HyperDoc.CBPV.Model.Base
open import HyperDoc.Lib hiding (trans)

open AlgHom
open Category
open Functor
open PshHom
open PshIso

module TypeStructure {Σ : Signature} (M : CBPVModel Σ)  where 
  open CBPVModel M

  HasV𝟙 : Type 
  HasV𝟙 = Representation V UnitPsh

  HasV𝟘 : Type 
  HasV𝟘 = Representation (V ^op) (UnitPsh {C = V ^op})

  HasC𝟘 : Type 
  HasC𝟘 = Representation (C ^op) (UnitPsh {C = C ^op})

  HasUTy : Type 
  HasUTy = (B : ob C) → Representation V (FORGET ∘F O[-, B ])

  Hasδ : Type 
  Hasδ = Σ[ Uty ∈ HasUTy ] ((B : ob C) → V [ Uty B .fst , Uty B .fst ])

  HasFTy : Type 
  HasFTy = (A : ob V) → Representation (C ^op) (FORGET ∘F O[ A ,-] ∘F from^op^op)

  HasO+ : Type
  HasO+ = (A A' : ob V) → 
    Σ[ A+A' ∈ V .ob ] 
      PshIso 
        (((Collage ^op) [-, inl A+A' ])) 
        (((Collage ^op) [-, inl A ]) ×Psh ((Collage ^op) [-, inl A' ]))

  Has⊕ : Type 
  Has⊕ = (B B' : ob C) → Representation (C ^op) (((C ^op) [-, B ]) ×Psh ((C ^op) [-, B' ]))
    
  HasO& : Type
  HasO& = (B B' : ob C) → 
    Σ[ B&B' ∈ C .ob ] 
      PshIso 
        (((Collage) [-, inr B&B' ])) 
        (((Collage) [-, inr B ]) ×Psh ((Collage) [-, inr B' ]))

  HasC& : Type
  HasC& = (B B' : ob C) → Representation C ((C [-, B ]) ×Psh (C [-, B' ])) 

  HasV× : Type
  HasV× = (A A' : ob V) → Representation V ((V [-, A ]) ×Psh (V [-, A' ])) 

  HasV+ : Type
  HasV+  = (A A' : ob V) → Representation (V ^op) (((V ^op) [-, A ]) ×Psh ((V ^op) [-, A' ]))

  module 𝟙Syntax (hasV𝟙 : HasV𝟙) where 
    𝟙 : ob V 
    𝟙 = hasV𝟙 .fst

    tt : {A : ob V} → V [ A , 𝟙 ] 
    tt {A} = hasV𝟙 .snd .nIso A .fst _

    𝟙η : {A : ob V}{t :  V [ A , 𝟙 ]}  → tt ≡ t
    𝟙η {A} {t} = hasV𝟙 .snd .nIso A .snd .snd t


  module USyntax (UTy : HasUTy) where 
    UProf : Profunctor C V _
    UProf = CurryBifunctorL (ParFunctorToBifunctor (FORGET {Σ} ∘F O))

    conv : (B : ob C) → Representation V (FORGET ∘F O[-, B ]) → Representation V (UProf .F-ob B)
    conv B r .fst = r .fst
    conv B r .snd .trans .N-ob = r .snd .trans .N-ob
    conv B r .snd .trans .N-hom = r .snd .trans .N-hom
    conv B r .snd .nIso x .fst = r .snd .nIso x .fst
    conv B r .snd .nIso x .snd .fst = r .snd .nIso x .snd .fst
    conv B r .snd .nIso x .snd .snd = r .snd .nIso x .snd .snd

    Ucomp : Functor C V 
    Ucomp = FunctorComprehension UProf λ B → reprToUniversalElement V (UProf .F-ob B) (conv B (UTy B))

    U : ob C → ob V 
    U = Ucomp  .F-ob

    thunk : {A : ob V}{B : ob C} → O'[ A , B ] → V [ A , U B ] 
    thunk {A}{B} = UTy B .snd .nIso A .fst 

    force : {B : ob C} → O'[ U B , B ]
    force {B} = UTy B .snd .trans .N-ob (U B) (V .id)

    force' : {A : ob V}{B : ob C} → V [ A , U B ]  → O'[ A , B ]
    force' {A}{B} V = UTy B .snd .trans .N-ob A V

    Uη' : {A : ob V}{B : ob C}{V : V [ A , U B ]} → thunk (force' V) ≡ V
    Uη' {A}{B}{V} = UTy B .snd .nIso A .snd .snd V

    forceSub : {A : ob V}{B : ob C} → (V : V [ A , U B ]) →  
      lcomp V .carmap force ≡ force' V
    forceSub {A}{B} V = 
      sym (UTy B .snd .trans  .N-hom _ _ V (CBPVModel.V M .id)) 
      ∙ cong force' (CBPVModel.V M .⋆IdR _) 
      -- {!   !} ∙ cong force' (CBPVModel.V M .⋆IdR _)
     --  sym (UTy B .snd .trans  .N-hom _ _ V (V .id)) ∙ cong force' ((V .⋆IdR _))

    Uη : {A : ob V}{B : ob C}{V : V [ A , U B ]} →  thunk (lcomp V .carmap force) ≡ V 
    Uη {A}{B}{V} = cong thunk (forceSub V) ∙ Uη'

    Uβ' : ∀ {A B}{M : O'[ A , B ]} → force' (thunk M) ≡ M
    Uβ' {A}{B}{M} = UTy B .snd .nIso A .snd .fst M

    Uβ : ∀{A B}{M : O'[ A , B ]} → lcomp (thunk M) .carmap force ≡ M
    Uβ {A}{B}{M} = forceSub (thunk M) ∙ Uβ'
    

  module FSyntax (FTy : HasFTy) where 
    open import  Cubical.Categories.Constructions.BinProduct 
    FProf : Profunctor (V ^op) (C ^op) _
    FProf = CurryBifunctor (ParFunctorToBifunctor ((FORGET {Σ} ∘F O) ∘F (Id ×F from^op^op)))
      
    conv : (A : ob V) → Representation (C ^op) (FORGET ∘F O[ A ,-] ∘F from^op^op) → Representation (C ^op) (F-ob FProf A)
    conv A r .fst = r .fst
    conv A r .snd .trans .N-ob = r .snd .trans .N-ob
    conv A r .snd .trans .N-hom c c' f p = r .snd .trans .N-hom c c' f p
    conv A r .snd .nIso x .fst = r .snd .nIso x .fst
    conv A r .snd .nIso x .snd .fst = r .snd .nIso x .snd .fst
    conv A r .snd .nIso x .snd .snd = r .snd .nIso x .snd .snd

    FComp : Functor V C 
    FComp = from^op^op ∘F ((FunctorComprehension FProf λ A → reprToUniversalElement (C ^op) (F-ob FProf A) (conv A (FTy A))) ^opF) ∘F to^op^op

    F : ob V → ob C 
    F = FComp .F-ob 

    bind : {A : ob V}{B : ob C} → O'[ A , B ] → C [ F A , B ] 
    bind {A}{B} M = FTy A .snd .nIso B .fst M

    ret : {A : ob V} → O'[ A , F A ] 
    ret {A} = FTy A .snd .trans .N-ob (F A) (C .id)

    ret' : {A : ob V}{B : ob C} → C [ F A , B ] → O'[ A , B ] 
    ret' {A}{B} = FTy A .snd .trans .N-ob B

    Fη' : {A : ob V}{B : ob C}{S : C [ F A , B ]} → bind (ret' S) ≡ S
    Fη' {A}{B}{S} = FTy A .snd .nIso B .snd .snd S

    Fβ' : ∀ {A B}{M : O'[ A , B ]} → ret' (bind M) ≡ M
    Fβ' {A}{B}{M} = FTy A .snd .nIso B .snd .fst M

    retSub : {A : ob V}{B : ob C} → (S : C [ F A , B ]) →  
      rcomp S .carmap ret ≡ ret' S
    retSub {A}{B} S =  
      sym (FTy A .snd .trans  .N-hom _ _ S (C .id) ) 
      ∙ cong (λ h → FTy A .snd .trans .N-ob B h) (C .⋆IdL _)

    Fη : {A : ob V}{B : ob C}{S : C [ F A , B ]} → bind (rcomp S .carmap ret) ≡ S
    Fη {A}{B}{S} = cong bind (retSub S) ∙ Fη'

    Fβ : ∀{A B}{M : O'[ A , B ]} → rcomp (bind M) .carmap ret ≡ M
    Fβ {A}{B}{M} = retSub (bind M) ∙ Fβ'

  module +Syntax (hasO+ : HasO+) where 

    _+_ : ob V → ob V → ob V 
    _+_ A A' = hasO+ A A' .fst

    σ₁' : {A A' A'' : ob V} → V [ A + A' , A'' ] →  V [ A , A'' ]
    σ₁' {A}{A'}{A''} f = hasO+ A A' .snd .trans .N-ob (inl A'') f .fst

    σ₁ : {A A' : ob V} → V [ A , A + A' ]
    σ₁ {A}{A'} = σ₁' (V .id)

    σ₁Sub : {A A' A'' : ob V} → (f : V [ A + A' , A'' ]) →  σ₁' f ≡ σ₁ ⋆⟨ V ⟩ f
    σ₁Sub {A}{A'}{A''} f = 
      (cong σ₁' (sym ( V .⋆IdL f )) ) ∙ 
      cong fst (hasO+ A A' .snd .trans .N-hom (inl A'') (inl (A + A')) f (V .id))

    σ₁c : {A A' : ob V}{B : ob C} → O'[ A + A' , B ] → O'[ A , B ]
    σ₁c {A}{A'}{B} f = hasO+ A A' .snd .trans .N-ob (inr B) f .fst

    σ₁cSub : {A A' : ob V}{B : ob C} → (f : O'[ A + A' , B ]) → σ₁c f ≡ lcomp σ₁ .carmap f
    σ₁cSub  {A}{A'}{B} f = cong σ₁c (sym lcompId) ∙ have where 
      have : σ₁c (lcomp (V .id) .carmap f) ≡ lcomp σ₁ .carmap f 
      have = cong fst (hasO+ A A' .snd .trans .N-hom (inr B)(inl (A + A')) f (V .id))

    σ₂' : {A A' A'' : ob V} → V [ A + A' , A'' ] →  V [ A' , A'' ]
    σ₂' {A}{A'}{A''} f = hasO+ A A' .snd .trans .N-ob (inl A'') f .snd

    σ₂ : {A A' : ob V} → V [ A' , A + A' ]
    σ₂ {A}{A'} = σ₂' (V .id)

    σ₂Sub : {A A' A'' : ob V} → (f : V [ A + A' , A'' ]) →  σ₂' f ≡ σ₂ ⋆⟨ V ⟩ f
    σ₂Sub {A}{A'}{A''} f = {!   !}

    σ₂c : {A A' : ob V}{B : ob C} → O'[ A + A' , B ] → O'[ A' , B ]
    σ₂c {A}{A'}{B} f = hasO+ A A' .snd .trans .N-ob (inr B) f .snd

    σ₂cSub : {A A' : ob V}{B : ob C} → (f : O'[ A + A' , B ]) → σ₂c f ≡ lcomp σ₂ .carmap f
    σ₂cSub  {A}{A'}{B} f = cong σ₂c (sym lcompId) ∙ have where 
      have : σ₂c (lcomp (V .id) .carmap f) ≡ lcomp σ₂ .carmap f 
      have = cong snd (hasO+ A A' .snd .trans .N-hom (inr B)(inl (A + A')) f (V .id))


    caseV : {A A' A'' : ob V} → V [ A , A'' ] → V [ A' , A'' ] → V [ A + A' , A'' ] 
    caseV {A}{A'}{A''} f g = hasO+ A A' .snd .nIso (inl A'') .fst (f , g)

    caseC : {A A' : ob V}{B : ob C} → O'[ A , B ] → O'[ A' , B ] → O'[ A + A' , B ] 
    caseC {A}{A'}{B} f g = hasO+ A A' .snd .nIso (inr B) .fst (f , g)

    caseCSub : {A A' : ob V}{B : ob C} → (f : O'[ A , B ]) → (g : O'[ A' , B ]) → caseC f g ≡ lcomp (caseV {!   !} {!   !}) .carmap {!   !}
    caseCSub {A}{A'}{B} f g = invPshIso  (hasO+ A A' .snd) .trans .N-hom {!   !} {!   !} {!   !} {!   !} 
    
    +β : {A A' A'' : ob V} → (f : V [ A , A'' ]) → (g : V [ A' , A'' ]) → (σ₁' (caseV f g) , σ₂' (caseV f g)) ≡ (f , g)
    +β {A}{A'}{A''} f g = hasO+ A A' .snd .nIso (inl A'') .snd .fst (f , g)

    +β₁' : {A A' A'' : ob V} → (f : V [ A , A'' ]) → (g : V [ A' , A'' ]) → σ₁' (caseV f g) ≡ f
    +β₁' {A}{A'}{A''} f g = cong fst (+β f g)

    +β₁ : {A A' A'' : ob V} → (f : V [ A , A'' ]) → (g : V [ A' , A'' ]) → σ₁ ⋆⟨ V ⟩ caseV f g ≡ f
    +β₁ {A}{A'}{A''} f g = sym (σ₁Sub (caseV f g)) ∙ +β₁' f g

    +β₂' : {A A' A'' : ob V} → (f : V [ A , A'' ]) → (g : V [ A' , A'' ]) → σ₂' (caseV f g) ≡ g
    +β₂' {A}{A'}{A''} f g = cong snd (+β f g)

    +β₂ : {A A' A'' : ob V} → (f : V [ A , A'' ]) → (g : V [ A' , A'' ]) → σ₂ ⋆⟨ V ⟩ caseV f g ≡ g
    +β₂ {A}{A'}{A''} f g = sym (σ₂Sub (caseV f g)) ∙ +β₂' f g

    +βc : {A A' : ob V}{B : ob C} → (f : O'[ A , B ]) → (g : O'[ A' , B ]) → (σ₁c (caseC f g) , σ₂c (caseC f g)) ≡ (f , g)
    +βc {A}{A'}{B} f g = hasO+ A A' .snd .nIso (inr B)  .snd .fst (f , g)

    +βc₁ : {A A' : ob V}{B : ob C} → (f : O'[ A , B ])(g : O'[ A' , B ]) → σ₁c (caseC f g) ≡ f 
    +βc₁ {A}{A'}{B} f g = cong fst (+βc f g )

    +βc₂ : {A A' : ob V}{B : ob C} → (f : O'[ A , B ])(g : O'[ A' , B ]) → σ₂c (caseC f g) ≡ g 
    +βc₂ {A}{A'}{B} f g = cong snd (+βc f g )


    +η : {A A' A'' : ob V} → (f : V [ A + A' , A'' ]) → caseV (σ₁' f) (σ₂' f) ≡ f   
    +η {A}{A'}{A''} f = hasO+ A A' .snd .nIso (inl A'') .snd .snd f