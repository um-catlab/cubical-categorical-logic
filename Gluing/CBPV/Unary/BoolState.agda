{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Unary.BoolState where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
import Cubical.Foundations.Equiv.Base as Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
open import Cubical.Data.Sigma

open import Cubical.Algebra.State
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.StateAlg.Vertical
open import Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.BoolState

open Category
open Functor
open Functorᴰ
open Section

private
  variable
    ℓ ℓ' : Level

module StateAlgGluing
  (BaseTy : Kind → Type ℓ)
  (Fun : ∀ {k1 k2} → ≤Kind k1 k2
    → CBPV.Ob BaseTy k1 → CBPV.Ob BaseTy k2 → Type ℓ')
  (𝟙 : BaseTy 𝒱)
  where
  open CBPV BaseTy
  open Terms Fun

  private
    L = ℓ-max ℓ ℓ'

  globalSections : Functorⱽ CBPV (StateAlgCBPV { ℓ = L } .fst)
  globalSections .F-obᴰ {x = 𝒱} A =
    (Tm tt (gen 𝟙) A , isSetTm)
  globalSections .F-obᴰ {x = 𝒞} B =
    ((Tm tt (gen 𝟙) B , isSetTm) , StateAlgEff (gen 𝟙) B)
  globalSections .F-homᴰ {x = 𝒱} {y = 𝒱} f M = seqS M f
  globalSections .F-homᴰ {x = 𝒱} {y = 𝒞} f M = seqS M f
  globalSections .F-homᴰ {x = 𝒞} {y = 𝒞} f =
    (λ M → seqS M f) , Plug-Homo f (gen 𝟙)
  globalSections .F-idᴰ {x = 𝒱} = funExt IdRS
  globalSections .F-idᴰ {x = 𝒞} =
    StateAlgHom≡ _ _ (funExt IdRS)
  globalSections .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒱} f g =
    funExt (λ M → sym (AssocS M f g))
  globalSections .F-seqᴰ {x = 𝒱} {y = 𝒱} {z = 𝒞} f g =
    funExt (λ M → sym (AssocS M f g))
  globalSections .F-seqᴰ {x = 𝒱} {y = 𝒞} {z = 𝒞} f g =
    funExt (λ M → sym (AssocS M f g))
  globalSections .F-seqᴰ {x = 𝒞} {y = 𝒞} {z = 𝒞} f g =
    StateAlgHom≡ _ _ (funExt (λ M → sym (AssocS M f g)))

  globalSectionsPreservesState :
    PreservesStateAlgEnrichment globalSections CBPVState StateAlgCBPVState
  globalSectionsPreservesState A B .Homo.rd-hom Mt Mf =
    funExt λ M → [r-homL] M Mt Mf
  globalSectionsPreservesState A B .Homo.wt-hom b M =
    funExt λ V → [w-homL] V b M

module BoolStateSyntax where
  data BaseTy : Kind → Type ℓ-zero where
    𝟙 BoolTy : BaseTy 𝒱

  open CBPV BaseTy

  data FUN : ∀ {k1 k2} → ≤Kind k1 k2
    → Ob k1 → Ob k2 → Type ℓ-zero where
    true false : FUN tt (gen 𝟙) (gen BoolTy)

  open Terms FUN public

  tru fls : Tm tt (gen 𝟙) (gen BoolTy)
  tru = gen true
  fls = gen false

  quoteBool : Bool → Tm tt (gen 𝟙) (gen BoolTy)
  quoteBool false = fls
  quoteBool true = tru

  BaseRelation : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝒱} tt (gen 𝟙) (gen X) → Type ℓ-zero
  BaseRelation 𝟙 V = V ≡ idS
  BaseRelation BoolTy V = Σ[ b ∈ Bool ] V ≡ quoteBool b

  hBaseRelation : ∀ {k} (X : BaseTy k)
    → Tm {k1 = 𝒱} tt (gen 𝟙) (gen X) → hSet ℓ-zero
  hBaseRelation X V .fst = BaseRelation X V
  hBaseRelation 𝟙 V .snd = isProp→isSet (isSetTm _ _)
  hBaseRelation BoolTy V .snd =
    isSetΣ isSetBool (λ _ → isProp→isSet (isSetTm _ _))

  module G = StateAlgGluing BaseTy FUN 𝟙

  module Fundamental = LocalElim
    G.globalSections
    StateAlgCBPVⱽ
    StateAlgCBPVState
    G.globalSectionsPreservesState
    (StateAlgCBPVStateᴰ ℓ-zero ℓ-zero)

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (StateAlgCBPVⱽ .fst)
        (k , G.globalSections .F-obᴰ (gen X))
  baseObject 𝟙 = hBaseRelation 𝟙
  baseObject BoolTy = hBaseRelation BoolTy

  fundamentalLemma :
    Section (∫F G.globalSections) (StateAlgCBPVⱽ .fst)
  fundamentalLemma =
    Fundamental.localElim baseObject
      λ { true V V≡id → true , cong₂ seqS V≡id refl ∙ IdLS tru
        ; false V V≡id → false , cong₂ seqS V≡id refl ∙ IdLS fls
        }

  LogicalRelation : ∀ {k} (Γ : Ob k)
    → Tm tt (gen 𝟙) Γ → hSet ℓ-zero
  LogicalRelation {k = 𝒱} Γ = Fundamental.local-obᴰ baseObject Γ
  LogicalRelation {k = 𝒞} Γ = Fundamental.local-obᴰ baseObject Γ .fst

  -- instantiate the open logical relation at the identity substitution.
  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt (gen 𝟙) Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt {k = 𝒱} {Γ = Γ} M = subst
    (λ N → ⟨ LogicalRelation Γ N ⟩)
    (IdLS M) $
    fundamentalLemma .F-homᴰ (_ , M) idS refl
  fundamentalAt {k = 𝒞} {Γ = Γ} M = subst
    (λ N → ⟨ LogicalRelation Γ N ⟩)
    (IdLS M) $
    fundamentalLemma .F-homᴰ (_ , M) idS refl

  private
    [ret]' : Tm tt (gen BoolTy) ([F] (gen BoolTy))
    [ret]' = CartesianLiftNotation.πⱽ (CBPV ^opᴰ)
      (MultCBPV .snd .snd (gen BoolTy))

    [ret]'≡ret : [ret]' ≡ [ret]
    [ret]'≡ret = cong snd
      (CBPV^op.reind-filler⁻ _
      ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))

  -- This is what the logical relation spits out. (after futzing with the identity substitution)
  --
  -- It says that every M : ClosedComp (F Bool)
  -- we construct a term s : Bool → Bool × (ClosedVal Bool)
  -- such that
  -- 1. M ≡ quote s so M ≡ rd (wt b1 (ret V1)) (wt b2 (ret V2)) (technicall [ret]' not [ret] b.c. of transport hell)
  -- 2. and each V1 , V2 is a canonical boolean value.
  RawFBool : Tm tt (gen 𝟙) ([F] (gen BoolTy)) → Type ℓ-zero
  RawFBool M =
    Σ[ (s , [ret]⟨s⟩≡M) ∈ Equiv.fiber
      (recFSA-f
        (Tm tt (gen 𝟙) (gen BoolTy))
        (StateAlgEff (gen 𝟙) ([F] (gen BoolTy)))
        (λ V → seqS V [ret]'))
      M ]
      (∀ b → Σ[ q ∈ Bool ] s b .snd ≡ quoteBool q)

  raw-FBool : ∀ M → RawFBool M
  raw-FBool = fundamentalAt

  interpretFreeStateBool :
    ⟨ FreeStateAlgebra (Bool , isSetBool) .fst ⟩
    → Tm tt (gen 𝟙) ([F] (gen BoolTy))
  interpretFreeStateBool = recFSA-f Bool
    (StateAlgEff (gen 𝟙) ([F] (gen BoolTy)))
    (λ b → seqS (quoteBool b) [ret])

  private
    rawState : ∀ {M} → RawFBool M
      → Bool → Bool × Tm tt (gen 𝟙) (gen BoolTy)
    rawState raw = raw .fst .fst

    rawRelated : ∀ {M} (raw : RawFBool M) b
      → Σ[ q ∈ Bool ] rawState raw b .snd ≡ quoteBool q
    rawRelated raw = raw .snd

    realizeRaw : ∀ {M} (raw : RawFBool M)
      → Equiv.fiber interpretFreeStateBool M
    realizeRaw raw .fst b .fst = rawState raw b .fst
    realizeRaw raw .fst b .snd = rawRelated raw b .fst
    realizeRaw raw .snd =
      -- this is just to paper over a stuck reind id
      cong₂ [rd]
        (cong ([wt] (rawState raw true .fst))
          (cong₂ seqS
            (sym (rawRelated raw true .snd)) (sym [ret]'≡ret)))
        (cong ([wt] (rawState raw false .fst))
          (cong₂ seqS
            (sym (rawRelated raw false .snd)) (sym [ret]'≡ret)))
      ∙ raw .fst .snd

  closed-FBool-surjective : ∀ M →
    Equiv.fiber interpretFreeStateBool M
  closed-FBool-surjective M = realizeRaw (raw-FBool M)

open BoolStateSyntax public
