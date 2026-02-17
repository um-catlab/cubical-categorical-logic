module Cubical.Categories.CBPV.SmallStep where 

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.List
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.List.Dependent

open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Category
open import Cubical.Categories.CBPV.Base
open import Cubical.Categories.CBPV.Functor
open import Cubical.Categories.CBPV.Instances.DefinedSubstitution hiding (F)
open import Cubical.Categories.CBPV.Instances.TransitionSystem
open import Cubical.Categories.Enriched.Functors.Base 
open import Cubical.Categories.Enriched.Instances.Presheaf.ChangeBase
open import Cubical.Categories.Enriched.Instances.FromCat
open import Cubical.Categories.Functor
open import Cubical.Categories.Monoidal.Enriched
open import Cubical.Categories.Monoidal.Instances.Presheaf
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.WithFamilies.Simple.Base 
open import Cubical.Categories.WithFamilies.Simple.Functor
open import Cubical.Categories.WithFamilies.Simple.Instances.Sets 
  renaming(SET to SETScwf)


  

open Functor
open Category 
open PshHom

clCtx : Ctx → Type ℓ-zero 
clCtx = Sub[ · ,_]

Fctx : Functor SubCat (SET ℓ-zero) 
Fctx .F-ob Γ = (clCtx Γ) , SubCat .isSetHom
Fctx .F-hom γ x = x ⋆⟨ SubCat ⟩ γ
Fctx .F-id = funExt (SubCat .⋆IdR)
Fctx .F-seq γ δ = funExt λ ρ → sym (SubCat .⋆Assoc _ _ _)

clVty : VTy → Type ℓ-zero 
clVty = · ⊢v_

Fvty : VTy → hSet ℓ-zero 
Fvty A = clVty A , isSetVal

-- NatTrans (vTm A) (SET[-, Fvty A] ∘ Fctx)
Fvtm : {A : VTy} → PshHet Fctx (vTm A) ((SET ℓ-zero)[-, Fvty A ]) 
Fvtm {A} .N-ob Γ v γ = subv γ v -- a closing substitution
Fvtm {A} .N-hom Δ Γ γ v = funExt λ Δ∙ → sym (subv⋆ Δ∙ γ v )

F : PreFunctor scwf (SETScwf ℓ-zero) 
F .fst = Fctx
F .snd .fst = Fvty
F .snd .snd = Fvtm
{-
𝓟 = PshMon.𝓟Mon SubCat ℓ-zero
𝓠 = PshMon.𝓟Mon (SET ℓ-zero) ℓ-zero

ℱ : CBPVFunctor CBPVDefSubst TSystemModel
𝓕 = {!   !}

_ : EnrichedCategory 𝓟 ℓ-zero
_ = stacks

-- This is exactly refl ...
-- yet it spins out...
_ : V ℓ-zero ≡ 𝓠 
_ = {!   !}

_ : {ℓ : Level} → V ℓ ≡ PshMon.𝓟Mon (SET ℓ) ℓ
_ = {!  refl !}
{-
wtf is going on here
why is this so slow to check...

  set = (SET ℓ)
  V = PshMon.𝓟Mon set ℓ
  E : EnrichedCategory V (ℓ-suc ℓ) 
  E = Cat→Enriched TSysCat
-}
_ : EnrichedCategory (V ℓ-zero) (ℓ-suc ℓ-zero)
_ = E ℓ-zero

_ : EnrichedCategory {! PshMon.𝓟Mon ? ?   !} {!   !} 
_ = BaseChange Fctx {!   !} {!   !} {!   !}
-}
{-
open import Cubical.Categories.Instances.TransitionSystem
_ = BaseChange Fctx ℓ-zero ℓ-zero {! Cat→Enriched TSysCat  !}

Fstk : EnrichedFunctor 𝓟 stacks {! BaseChange Fctx ? ? ?  !} 
Fstk = {!   !}
-}
-- ℱ : CBPVFunctor CBPVDefSubst TSystemModel
-- 𝓕 = {!   !}