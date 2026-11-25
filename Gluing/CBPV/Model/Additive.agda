-- A canonicity proof for CBPV enriched in an algebraic theory.
--
-- The global sections/Points functor preserves value coproducts and
-- F.
--
-- As a corollary we get canonicity for any finite coproduct of 1:
-- Free n → Comp (F ⌈ n ⌉) is an isomorphism of algebras

{-# OPTIONS --prop --lossy-unification #-}
module Gluing.CBPV.Model.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
  using (Iso; compIso; invIso; LiftIso; _Iso⟨_⟩_; _∎Iso)
open import Cubical.Foundations.Structure

open import Cubical.Prop

open import Cubical.Data.Bool as Bool hiding (elim)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Unit

open import Cubical.Algebra.Theory.Base

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism.More
import Cubical.Categories.Isomorphism as CatIso
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞;
    ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section.Base
  renaming (Section to DisplayedSection)
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Enrichment.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Codomain.Model
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Free.ModelEnriched.Additive
open import Cubical.Categories.Displayed.Instances.Algebra.Model

open Category
open Functor
open Functorᴰ
open DisplayedSection

private
  variable
    ℓO ℓA ℓE ℓEA : Level

-- The logical-relations model is parameterized by the ordinary and displayed
-- free-model universal properties used to interpret F.
module ModelGluing
  (T : Theory ℓO ℓA ℓE ℓEA)
  (BaseTy : Kind → Type (ModelLevel T))
  (Fun : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → CBPV.Ob T BaseTy k₁ → CBPV.Ob T BaseTy k₂
    → Type (ModelLevel T))
  (I : CBPV.Ob T BaseTy 𝒱)
  where
  open CBPV T BaseTy
  open Terms Fun

  pts : Functorⱽ (AddCBPV .fst .fst) (ModelCBPV T .fst)
  pts = points T (AddCBPV .fst .fst) CBPVModel I

  ptsPreservesModel : PreservesModelEnrichment T pts
    CBPVModel (ModelCBPVModel T)
  ptsPreservesModel =
    pointsPreservesModel T (AddCBPV .fst .fst) CBPVModel I

module BoolModelSyntax
  (T : Theory ℓO ℓA ℓE ℓEA)
  where
  open Theory T

  private
    L = ModelLevel T

  LiftBool : hSet L
  LiftBool = Lift L Bool , isOfHLevelLift 2 isSetBool

  data BaseTy (k : Kind) : Type L where

  open CBPV T BaseTy

  data FUN : ∀ {k₁ k₂} → ≤Kind k₁ k₂
    → Ob k₁ → Ob k₂ → Type L where

  open Terms FUN public

  UnitTy BoolTy : VTy
  UnitTy = [1]
  BoolTy = UnitTy [+] UnitTy

  FBoolTy : Ob 𝒞
  FBoolTy = [F] BoolTy

  tru fls : Tm tt UnitTy BoolTy
  tru = [+I1]
  fls = [+I2]

  quoteBool : Bool → Tm tt UnitTy BoolTy
  quoteBool false = fls
  quoteBool true = tru

  module G = ModelGluing T BaseTy FUN UnitTy

  module Fundamental = LocalElim
    G.pts
    (ModelCodAddⱽ T)
    (ModelCBPVModel T)
    G.ptsPreservesModel
    (ModelCodModel T)
    ⦃ ModelCodReind T ⦄

  baseObject : ∀ {k} (X : BaseTy k)
    → Categoryᴰ.ob[_] (ModelCod T) (k , G.pts .F-obᴰ (gen X))
  baseObject ()

  fundamentalLemma : DisplayedSection (∫F G.pts) (ModelCod T)
  fundamentalLemma = Fundamental.localElim baseObject λ ()

  LogicalRelation : ∀ {k} (Γ : Ob k)
    → Tm tt UnitTy Γ → hSet L
  LogicalRelation {k = 𝒱} Γ = Fundamental.local-obᴰ baseObject Γ
  LogicalRelation {k = 𝒞} Γ = Fundamental.local-obᴰ baseObject Γ .fst

  canonical : ∀ {k} {Γ : Ob k} (M : Tm tt UnitTy Γ)
    → Σ[ w ∈ Σ _ (λ N → ⟨ LogicalRelation Γ N ⟩) ] w .fst ≡ M
  canonical {k = 𝒱} M =
    run .fst .snd (idS , tt*) , (λ i → run .snd i .snd (idS , tt*)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)
  canonical {k = 𝒞} M =
    run .fst .snd (idS , tt*) , (λ i → run .snd i .snd (idS , tt*)) ∙ IdLS M
    where run = fundamentalLemma .F-homᴰ (_ , M)

  fundamentalAt : ∀ {k} {Γ : Ob k} (M : Tm tt UnitTy Γ)
    → ⟨ LogicalRelation Γ M ⟩
  fundamentalAt {Γ = Γ} M = subst (λ N → ⟨ LogicalRelation Γ N ⟩)
    (canonical M .snd) (canonical M .fst .snd)

  Val : VTy → hSet L
  Val A = G.pts .F-obᴰ A

  Val1≅Unit : Iso ⟨ Val UnitTy ⟩ (Unit* {L})
  Val1≅Unit =
    pointsPreserveTerminal T (AddCBPV .fst .fst) CBPVModel UnitTy
      value-terminalⱽ

  pointsPreserve0 : Iso (Empty.⊥* {L}) ⟨ Val [0] ⟩
  pointsPreserve0 .Iso.fun = Empty.rec*
  pointsPreserve0 .Iso.inv = fundamentalAt
  pointsPreserve0 .Iso.sec V = Empty.rec* (fundamentalAt V)
  pointsPreserve0 .Iso.ret ()

  module PointsPreserve+ (A B : VTy) where
    join : ⟨ Val A ⟩ ⊎ ⟨ Val B ⟩ → ⟨ Val (A [+] B) ⟩
    join = Sum.rec (λ V → seqS V [+I1]) (λ V → seqS V [+I2])

    splitRelated : ∀ {V} → ⟨ LogicalRelation (A [+] B) V ⟩
      → ⟨ Val A ⟩ ⊎ ⟨ Val B ⟩
    splitRelated (inl ((V , _) , _)) = inl V
    splitRelated (inr ((V , _) , _)) = inr V

    join-splitRelated : ∀ {V} (Vᴰ : ⟨ LogicalRelation (A [+] B) V ⟩)
      → join (splitRelated Vᴰ) ≡ V
    join-splitRelated (inl ((V , _) , p)) =
      sym (cong (seqS V) σ₁ⱽ≡[+I1]) ∙ p
    join-splitRelated (inr ((V , _) , p)) =
      sym (cong (seqS V) σ₂ⱽ≡[+I2]) ∙ p

    split : ⟨ Val (A [+] B) ⟩ → ⟨ Val A ⟩ ⊎ ⟨ Val B ⟩
    split V = splitRelated (canonical V .fst .snd)

    join-split : ∀ V → join (split V) ≡ V
    join-split V =
      join-splitRelated (canonical V .fst .snd) ∙ canonical V .snd

    split-join : ∀ V → split (join V) ≡ V
    split-join (inl V) = cong inl (canonical V .snd)
    split-join (inr V) = cong inr (canonical V .snd)

    pointsPreserve+ : Iso (⟨ Val A ⟩ ⊎ ⟨ Val B ⟩) ⟨ Val (A [+] B) ⟩
    pointsPreserve+ .Iso.fun = join
    pointsPreserve+ .Iso.inv = split
    pointsPreserve+ .Iso.sec = join-split
    pointsPreserve+ .Iso.ret = split-join

  -- The points functor preserves F: for every value type A the
  -- homomorphism Free (Val A) → Comp (F A) induced by V ↦ V ⋆ ret is an
  -- isomorphism.
  module PointsPreserveF (A : VTy) where
    ValA : hSet L
    ValA = G.pts .F-obᴰ A

    CompFA : Category.ob (MODEL T L)
    CompFA = ModelEnrichmentModel CBPV T CBPVModel UnitTy ([F] A)

    FreeValA : Category.ob (MODEL T L)
    FreeValA = FreeModel ⟨ ValA ⟩

    ηA : ⟨ ValA ⟩ → ⟨ FreeValA .fst ⟩
    ηA = var

    retA : Tm tt A ([F] A)
    retA = [ret]

    module OF = PushᶠNotation T {A = ValA} {B = CompFA}
      (λ V → seqS V retⱽ) (LogicalRelation A)

    module FreeA = UniversalElementNotation (MODELFree T ValA)
    module Free∫ = UniversalElementNotation (MODELFree T OF.∫Aᴰ)

    -- The homomorphism induced by V ↦ V ⋆ ret.
    recA : MODEL T L [ FreeValA , CompFA ]
    recA = FreeA.intro (λ V → seqS V retA)

    recAβ : ∀ V → recA .fst (ηA V) ≡ seqS V retA
    recAβ = funExt⁻ (FreeA.β {c = CompFA} {p = λ V → seqS V retA})

    section∫ : ⟨ CompFA .fst ⟩ → ⟨ OF.Free∫ .fst ⟩
    section∫ M = canonical M .fst .snd .fst

    h-section∫ : ∀ M → OF.h .fst (section∫ M) ≡ M
    h-section∫ M = canonical M .fst .snd .snd ∙ canonical M .snd

    section∫Homo : MODEL T L [ CompFA , OF.Free∫ ]
    section∫Homo .fst = section∫
    section∫Homo .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ = cong section∫ op∘γ≡op⟨γ⟩

    Freeπ₁ : MODEL T L [ OF.Free∫ , FreeValA ]
    Freeπ₁ = Free∫.intro (λ x → ηA (x .fst))

    Freeπ₁β : ∀ x → Freeπ₁ .fst (var x) ≡ ηA (x .fst)
    Freeπ₁β = funExt⁻ (Free∫.β {c = FreeValA} {p = λ x → ηA (x .fst)})

    Freeπ₁-recA : (Freeπ₁ ⋆⟨ MODEL T L ⟩ recA) ≡ OF.h
    Freeπ₁-recA = Free∫.extensionality (funExt λ x →
      cong (recA .fst) (Freeπ₁β x) ∙ recAβ (x .fst)
      ∙ cong (seqS (x .fst)) (sym retⱽ≡[ret]))

    sectionA : ⟨ CompFA .fst ⟩ → ⟨ FreeValA .fst ⟩
    sectionA M = Freeπ₁ .fst (section∫ M)

    sectionAHomo : MODEL T L [ CompFA , FreeValA ]
    sectionAHomo = section∫Homo ⋆⟨ MODEL T L ⟩ Freeπ₁

    recA-sectionA : ∀ M → recA .fst (sectionA M) ≡ M
    recA-sectionA M =
      funExt⁻ (cong fst Freeπ₁-recA) (section∫ M) ∙ h-section∫ M

    sectionA-ret : ∀ V → sectionA (seqS V retA) ≡ ηA V
    sectionA-ret V = Freeπ₁β (canonical V .fst) ∙ cong ηA (canonical V .snd)

    sectionA-recA :
      (recA ⋆⟨ MODEL T L ⟩ sectionAHomo) ≡ Category.id (MODEL T L)
    sectionA-recA = FreeA.extensionality (funExt λ V →
      cong sectionA (recAβ V) ∙ sectionA-ret V)

    pointsPreserveF : CatIso (MODEL T L) FreeValA CompFA
    pointsPreserveF .fst = recA
    pointsPreserveF .snd .isIso.inv = sectionAHomo
    pointsPreserveF .snd .isIso.sec =
      isFaithfulMODELForget T _ _ _ _ (funExt recA-sectionA)
    pointsPreserveF .snd .isIso.ret = sectionA-recA

  -- Boolean canonicity is the composite
  -- Free (Lift Bool) ≅ Free (Val (1 + 1)) ≅ Comp (F (1 + 1)).
  private
    module PF = PointsPreserveF BoolTy

    Bool≅Unit⊎Unit : Iso (Lift L Bool) (Unit* {L} ⊎ Unit* {L})
    Bool≅Unit⊎Unit =
      Lift L Bool
        Iso⟨ invIso LiftIso ⟩
      Bool
        Iso⟨ invIso Iso-⊤⊎⊤-Bool ⟩
      Unit ⊎ Unit
        Iso⟨ ⊎Iso LiftIso LiftIso ⟩
      Unit* ⊎ Unit*
        ∎Iso

  Bool≅ValBool : Iso (Lift L Bool) ⟨ Val BoolTy ⟩
  Bool≅ValBool = compIso Bool≅Unit⊎Unit
    (compIso (⊎Iso (invIso Val1≅Unit) (invIso Val1≅Unit))
      (PointsPreserve+.pointsPreserve+ UnitTy UnitTy))

  private
    Bool≅ValBool-quote : ∀ b
      → Bool≅ValBool .Iso.fun b ≡ quoteBool (lower b)
    Bool≅ValBool-quote (lift false) =
      cong (λ V → seqS V fls) (sym ([1η] idS)) ∙ IdLS fls
    Bool≅ValBool-quote (lift true) =
      cong (λ V → seqS V tru) (sym ([1η] idS)) ∙ IdLS tru

  SyntaxMODEL : Category.ob (MODEL T L)
  SyntaxMODEL = PF.CompFA

  FreeBoolMODEL : Category.ob (MODEL T L)
  FreeBoolMODEL = FreeModel ⟨ LiftBool ⟩

  private
    module P+ = PointsPreserve+ UnitTy UnitTy
    module Free∫ = UniversalElementNotation (MODELFree T PF.OF.∫Aᴰ)

    freeBool≅Val : CatIso (MODEL T L) FreeBoolMODEL PF.FreeValA
    freeBool≅Val = FreeMODELIso T {X = LiftBool} {Y = Val BoolTy} Bool≅ValBool

    decodeGen : ⟨ PF.OF.∫Aᴰ ⟩ → ⟨ FreeBoolMODEL .fst ⟩
    decodeGen x =
      var (Bool≅ValBool .Iso.inv (P+.join (P+.splitRelated (x .snd))))

    decodeBool : MODEL T L [ PF.OF.Free∫ , FreeBoolMODEL ]
    decodeBool = Free∫.intro decodeGen

    decodeBool≡ : decodeBool
      ≡ PF.Freeπ₁ ⋆⟨ MODEL T L ⟩ freeBool≅Val .snd .isIso.inv
    decodeBool≡ = Free∫.extensionality (funExt λ x →
      funExt⁻ (Free∫.β {c = FreeBoolMODEL} {p = decodeGen}) x
      ∙ cong (λ V → var (Bool≅ValBool .Iso.inv V))
          (P+.join-splitRelated (x .snd))
      ∙ sym (cong (freeBool≅Val .snd .isIso.inv .fst) (PF.Freeπ₁β x)))

  freeBool≅Syntax : CatIso (MODEL T L) FreeBoolMODEL SyntaxMODEL
  freeBool≅Syntax = improveCatIso (CatIso.⋆Iso freeBool≅Val PF.pointsPreserveF)
    (_ , refl)
    (_ , sym (cong (λ g → PF.section∫Homo ⋆⟨ MODEL T L ⟩ g) decodeBool≡
      ∙ sym (MODEL T L .⋆Assoc _ _ _)))

  private
    ηBool : Lift L Bool → ⟨ FreeBoolMODEL .fst ⟩
    ηBool = var

    interpretGen : Lift L Bool → ⟨ SyntaxMODEL .fst ⟩
    interpretGen b = seqS (quoteBool (lower b)) [ret]

    interpretFreeBoolHomo : MODEL T L [ FreeBoolMODEL , SyntaxMODEL ]
    interpretFreeBoolHomo = freeBool≅Syntax .fst

    interpretβ : (λ b → interpretFreeBoolHomo .fst (ηBool b)) ≡ interpretGen
    interpretβ = funExt λ b →
      PF.recAβ (Bool≅ValBool .Iso.fun b)
      ∙ cong (λ V → seqS V [ret]) (Bool≅ValBool-quote b)

  interpretFreeBool :
    ⟨ FreeBoolMODEL .fst ⟩ → Tm tt UnitTy ([F] BoolTy)
  interpretFreeBool = interpretFreeBoolHomo .fst

  unquote-FBool : Tm tt UnitTy ([F] BoolTy) → ⟨ FreeBoolMODEL .fst ⟩
  unquote-FBool = freeBool≅Syntax .snd .isIso.inv .fst

  interpret-unquote-FBool : ∀ M
    → interpretFreeBool (unquote-FBool M) ≡ M
  interpret-unquote-FBool =
    funExt⁻ (cong fst (freeBool≅Syntax .snd .isIso.sec))

  unquote-interpret-FBool : ∀ t
    → unquote-FBool (interpretFreeBool t) ≡ t
  unquote-interpret-FBool =
    funExt⁻ (cong fst (freeBool≅Syntax .snd .isIso.ret))
