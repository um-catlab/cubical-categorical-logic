{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Equiv.Dependent.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More hiding (_≡[_]_; rectify)
open import Cubical.Foundations.HLevels.More

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable hiding (Elements)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
import Cubical.Categories.Displayed.Instances.Sets.Base as Setᴰ
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq

import Cubical.Categories.Displayed.Presheaf.Base as Curried
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base

import Cubical.Categories.Displayed.Limits.CartesianV' as Path
import Cubical.Categories.Displayed.Limits.CartesianClosedV as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Base as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier as Path
import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration as Path

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level
    ℓA ℓB ℓAᴰ ℓBᴰ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level
    ℓD ℓD' ℓDᴰ ℓDᴰ' : Level
    ℓE ℓE' ℓEᴰ ℓEᴰ' : Level
    ℓP ℓQ ℓR ℓPᴰ ℓPᴰ' ℓQᴰ ℓQᴰ' ℓRᴰ : Level


-- Cleanest formulation of this theorem is that for *any* proofs of Eq.LRⱽ xᴰ and Path.LRⱽ xᴰ, that we get the right kind of square

module _ {C : Category ℓC ℓC'}(⋆AssocC : ReprEqAssoc C)(⋆IdLC : EqIdL C)(Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {x} (xᴰ : Cᴰ.ob[ x ]) (xᴰLRⱽEq : LRⱽ Cᴰ ⋆AssocC xᴰ) (xᴰLRⱽPath : Path.isLRⱽObᴰ Cᴰ xᴰ) where
    private
      module LRⱽPath = Path.LRⱽPresheafᴰNotation Cᴰ ((Cᴰ Path.[-][-, xᴰ ]) , xᴰLRⱽPath)
      module LRⱽEq = LRⱽNotation Cᴰ ⋆AssocC xᴰLRⱽEq
    -- (Γ , Γᴰ , p) → (Γ , Γᴰ ×ⱽ p* x , p)
    ×LRⱽ-Path/→Eq/-square-Iso : ∀ Γ3 → CatIso (Cᴰ / (C [-, x ]))
      ((LRⱽF Cᴰ ⋆AssocC ⋆IdLC xᴰ xᴰLRⱽEq ∘F Path/→Eq/ (C [-, x ]) Cᴰ) ⟅ Γ3 ⟆)
      ((Path/→Eq/ (C [-, x ]) Cᴰ ∘F
        Path.×LRⱽPshᴰ (Path.LRⱽObᴰ→LRⱽ Cᴰ (xᴰ , xᴰLRⱽPath)))
       ⟅ Γ3 ⟆)
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .fst .fst = C.id
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .fst .snd .fst =
      LRⱽPath.introᴰ
        (Iso.fun (xᴰLRⱽEq Γᴰ f .snd .PshIsoEq.isos (Γ , xᴰLRⱽEq Γᴰ f .fst , C.id)) Cᴰ.idᴰ .fst)
        (Iso.fun (xᴰLRⱽEq Γᴰ f .snd .PshIsoEq.isos (Γ , xᴰLRⱽEq Γᴰ f .fst , C.id)) Cᴰ.idᴰ .snd)
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .fst .snd .snd = ⋆IdLC f
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .snd .isIso.inv .fst = C.id
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .snd .isIso.inv .snd .fst =
      Iso.inv (xᴰLRⱽEq Γᴰ f .snd .PshIsoEq.isos (Γ , xᴰLRⱽPath Γᴰ f .fst , C.id)) (LRⱽPath.π₁ⱽ , LRⱽPath.π₂ⱽ)
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .snd .isIso.inv .snd .snd = ⋆IdLC f
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .snd .isIso.sec = Hom/≡ $
      LRⱽPath.extensionalityᴰ
        (LRⱽPath.⋆π₁ⱽ-natural _ _
        ∙ Cᴰ.⟨⟩⋆⟨ LRⱽPath.β₁ⱽ' _ _ ⟩
        ∙ LRⱽEq.β₁ⱽ _ _)
        (LRⱽPath.⋆π₂ⱽ-natural _ _
        ∙ Cᴰ.reind-filler⁻ _
        ∙ Cᴰ.⟨⟩⋆⟨ LRⱽPath.β₂ⱽ' _ _ ⟩
        ∙ LRⱽEq.β₂ⱽ _ _)
    ×LRⱽ-Path/→Eq/-square-Iso Γ3@(Γ , Γᴰ , f) .snd .isIso.ret = Hom/≡ $
      LRⱽEq.extensionalityᴰ
        (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ LRⱽEq.β₁ⱽ _ _ ⟩ ∙ LRⱽPath.β₁ⱽ _ _ ∙ sym (Cᴰ.⋆IdL _))
        (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨⟩⋆⟨ LRⱽEq.β₂ⱽ _ _ ⟩ ∙ Cᴰ.reind-filler _ ∙ LRⱽPath.β₂ⱽ _ _ ∙ sym (Cᴰ.⋆IdL _))

    ×LRⱽ-Path/→Eq/-square : NatIso
      (LRⱽF Cᴰ ⋆AssocC ⋆IdLC xᴰ xᴰLRⱽEq ∘F Path/→Eq/ (C [-, x ]) Cᴰ)
      (Path/→Eq/ ((C [-, x ])) Cᴰ ∘F Path.×LRⱽPshᴰ (Path.LRⱽObᴰ→LRⱽ Cᴰ (xᴰ , xᴰLRⱽPath)))
    ×LRⱽ-Path/→Eq/-square = isosToNatIso
      ×LRⱽ-Path/→Eq/-square-Iso
      λ Δ3 Γ3 f3@(γ , γᴰ , tri) → Hom/≡
        (LRⱽPath.extensionalityᴰ
          (LRⱽPath.⋆π₁ⱽ-natural _ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ LRⱽPath.β₁ⱽ' _ _ ⟩
          ∙ LRⱽEq.β₁ⱽ _ _ ∙ sym (Cᴰ.reindEq-filler (⋆IdLC γ))
          -- Eq.π₁ⱽ Cᴰ.⋆ᴰ γᴰ
          ∙ sym (LRⱽPath.⋆π₁ⱽ-natural _ _
            ∙ Cᴰ.⟨ refl ⟩⋆⟨ LRⱽPath.β₁ⱽ' _ _ ⟩
            ∙ sym (Cᴰ.⋆Assoc _ _ _)
            ∙ Cᴰ.⟨ LRⱽPath.β₁ⱽ _ _ ⟩⋆⟨⟩))
          (LRⱽPath.⋆π₂ⱽ-natural _ _
          ∙ Cᴰ.reind-filler⁻ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ LRⱽPath.β₂ⱽ' _ _ ⟩
          ∙ LRⱽEq.β₂ⱽ _ _
          ∙ sym (Cᴰ.reindEq-filler (Eq.sym (Eq.pathToEq tri)))
          ∙ sym (Cᴰ.reindEq-filler (⋆IdLC (Δ3 .snd .snd)))
          ∙ sym (LRⱽPath.⋆π₂ⱽ-natural _ _
          ∙ Cᴰ.reind-filler⁻ _
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ LRⱽPath.β₂ⱽ' _ _ ∙ Cᴰ.reind-filler⁻ _ ∙ Cᴰ.reind-filler⁻ _ ⟩
          ∙ Cᴰ.reind-filler _ -- scary
          ∙ LRⱽPath.β₂ⱽ _ _)))
  module _
    (bp : BinProducts C)
    (cartLifts : Fibration Cᴰ ⋆AssocC)
    (π₁NatEqC : Allπ₁NatEq bp)
    (×aF-seqC : All×aF-seq bp)
    {Γ A : C.ob}
    where
    private
      module bp = BinProductsNotation bp
    module _ (π₁Quadrable : ∀ Γ → Path.Quadrable Cᴰ (BinProductsWithNotation.π₁ (λ Γ₂ → bp (Γ₂ , A)))) (Aᴰ : Cᴰ.ob[ Γ bp.× A ]) where
      private
        module fibEq = FibrationNotation Cᴰ ⋆AssocC cartLifts
        module π₁* {Γ} = Path.QuadrableNotation Cᴰ (π₁Quadrable Γ)

      wkF-Path/→Eq/-square-iso : ∀ Δ3 → CatIso
        (Cᴰ /
         (C [-, ((λ Γ₁ → bp (Γ₁ , A)) BinProductsWithNotation.×a) Γ ]))
        ((wkF Cᴰ ⋆IdLC ⋆AssocC cartLifts A (λ Γ₁ → bp (Γ₁ , A))
          (π₁NatEqC A) (×aF-seqC A) Γ
          ∘F Path/→Eq/ (C [-, Γ ]) Cᴰ)
         ⟅ Δ3 ⟆)
        ((Path/→Eq/ (C [-, Γ bp.× A ]) Cᴰ ∘F
          Path.wkF (Path.π₁Quant Cᴰ A (λ Γ₁ → bp (Γ₁ , A)) π₁Quadrable) Γ)
         ⟅ Δ3 ⟆)
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .fst .fst = C.id
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .fst .snd .fst = π₁*.introᴰ fibEq.πⱽ
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .fst .snd .snd = ⋆IdLC _
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .snd .isIso.inv .fst = C.id
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .snd .isIso.inv .snd .fst = fibEq.introᴰ π₁*.πⱽ
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .snd .isIso.inv .snd .snd = ⋆IdLC _
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .snd .isIso.sec = Hom/≡ (π₁*.extensionalityᴰ (C.⋆IdL _) $
        π₁*.⋆πⱽ-natural
        ∙ Cᴰ.⟨⟩⋆⟨ π₁*.βᴰ _ ⟩
        ∙ fibEq.βᴰ)
      wkF-Path/→Eq/-square-iso Δ3@(Δ , Δᴰ , γ) .snd .isIso.ret = Hom/≡ (fibEq.extensionalityᴰ (C.⋆IdL _) $
        Cᴰ.⋆Assoc _ _ _
        ∙ Cᴰ.⟨⟩⋆⟨ fibEq.βᴰ ⟩
        ∙ π₁*.βᴰ' _
        ∙ (sym $ Cᴰ.⋆IdL _))

      wkF-Path/→Eq/-square :
        NatIso (wkF Cᴰ ⋆IdLC ⋆AssocC cartLifts A (λ Γ → bp (Γ , A)) (π₁NatEqC A) (×aF-seqC A) Γ ∘F Path/→Eq/ (C [-, Γ ]) Cᴰ)
               (Path/→Eq/ (C [-, Γ bp.× A ]) Cᴰ ∘F Path.wkF (Path.π₁Quant Cᴰ A ((λ Γ → bp (Γ , A))) π₁Quadrable) Γ)
      wkF-Path/→Eq/-square = isosToNatIso wkF-Path/→Eq/-square-iso
        λ Θ3 Δ3 δ3@(δ , δᴰ , tri) →
          Hom/≡ (π₁*.extensionalityᴰ (C.⋆IdR _ ∙ sym (C.⋆IdL _))
            (π₁*.⋆πⱽ-natural
            ∙ Cᴰ.⟨⟩⋆⟨ π₁*.βᴰ _ ⟩
            ∙ fibEq.βᴰ
            ∙ Cᴰ.reindEq-filler⁻ ((Eq.sym $ π₁NatEqC A δ))
            ∙ Cᴰ.⟨ Cᴰ.reindEq-filler⁻ (⋆IdLC _) ⟩⋆⟨⟩
            ∙ sym (π₁*.⋆πⱽ-natural
            ∙ Cᴰ.⟨⟩⋆⟨ π₁*.βᴰ _ ∙ Cᴰ.reind-filler⁻ _ ⟩
            ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ π₁*.βᴰ' _ ⟩⋆⟨⟩)))

module _ (CC : CartesianCategory ℓC ℓC') where
  private
    module CC = CartesianCategory CC
  module _ (⋆AssocC : ReprEqAssoc CC.C)
           (⋆IdLC : EqIdL CC.C)
           (π₁NatEqC : Allπ₁NatEq CC.bp)
           (×aF-seqC : All×aF-seq CC.bp)
           (Cᴰ : Categoryᴰ CC.C ℓCᴰ ℓCᴰ') where
    EqCCCⱽ→CCCⱽ : isCartesianClosedⱽ {C = CC.C} ⋆AssocC Cᴰ ⋆IdLC CC.bp π₁NatEqC ×aF-seqC
      → Path.CartesianClosedCategoryⱽ CC ℓCᴰ ℓCᴰ'
    EqCCCⱽ→CCCⱽ isCCCⱽ .Path.CartesianClosedCategoryⱽ.CCⱽ = EqCCⱽ→CCⱽ ⋆AssocC Cᴰ (isCCCⱽ .fst)
    EqCCCⱽ→CCCⱽ isCCCⱽ .Path.CartesianClosedCategoryⱽ.lrⱽ =
      Path.BinProductsⱽ+Fibration→AllLRⱽ (Path.CartesianCategoryⱽ.Cᴰ
                                           (Path.CartesianClosedCategoryⱽ.CCⱽ (EqCCCⱽ→CCCⱽ isCCCⱽ)))
                                           ((EqCCⱽ→CCⱽ ⋆AssocC Cᴰ (isCCCⱽ .fst)) .Path.CartesianCategoryⱽ.bpⱽ)
                                           ((EqCCⱽ→CCⱽ ⋆AssocC Cᴰ (isCCCⱽ .fst)) .Path.CartesianCategoryⱽ.cartesianLifts)
    EqCCCⱽ→CCCⱽ isCCCⱽ .Path.CartesianClosedCategoryⱽ.expⱽ {x} xᴰ yᴰ =
      EqReprⱽ→PathReprⱽ _ (isCCCⱽ .snd .fst xᴰ yᴰ)
      -- reindPsh Path/→Eq/ $ reindPsh (Eq.×LRⱽ xᴰ) $ Cᴰ Eq.[-][-, yᴰ ]
      Path.◁PshIsoⱽ reindPsh-square _ _ _ _ _ (×LRⱽ-Path/→Eq/-square ⋆AssocC ⋆IdLC _ xᴰ _ _)
      Path.⋆PshIsoⱽ reindPshIso (Path.×LRⱽPshᴰ
                                  (Path.LRⱽObᴰ→LRⱽ
                                   (Path.CartesianCategoryⱽ.Cᴰ
                                    (Path.CartesianClosedCategoryⱽ.CCⱽ (EqCCCⱽ→CCCⱽ isCCCⱽ)))
                                   (xᴰ , Path.CartesianClosedCategoryⱽ.lrⱽ (EqCCCⱽ→CCCⱽ isCCCⱽ) xᴰ))) Representable≅
    EqCCCⱽ→CCCⱽ isCCCⱽ .Path.CartesianClosedCategoryⱽ.forallⱽ {Γ} {A} Aᴰ =
      EqReprⱽ→PathReprⱽ _ (isCCCⱽ .snd .snd A Aᴰ)
      Path.◁PshIsoⱽ reindPsh-square (Path/→Eq/ (CC.C [-, Γ ]) Cᴰ) _ _ (Path/→Eq/ (CC.C [-, Γ CC.× A ]) Cᴰ) _
        (wkF-Path/→Eq/-square ⋆AssocC ⋆IdLC Cᴰ CC.bp (isCCCⱽ .fst .snd .snd) π₁NatEqC ×aF-seqC _ (isCCCⱽ .fst .fst (Γ CC.× A) .fst))
      Path.⋆PshIsoⱽ reindPshIso _ Representable≅
