{-

  Reindexing a displayed monoidal cat along a pair of an oplax
  monoidal functor and a lax monoidal functor inherits a displayed
  monoidal structure if we have (op)cartesian lifts of the (op)lax
  data.

  So far we only need this where we have hasPropHoms, so this is not
  as general as it could be.

-}

module Cubical.Categories.Displayed.Instances.Reindex.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Instances.BinProduct
open import Cubical.Categories.Instances.BinProduct.Monoidal
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Functor


open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
import      Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Instances.Reindex.Properties
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Fibration.TwoSided
open import Cubical.Categories.Displayed.Fibration.IsoFibration

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open NatTrans
open NatIso
open isIso

module _ {M : MonoidalCategory ℓC ℓC'}
         {N : MonoidalCategory ℓD ℓD'}
         (P : MonoidalCategoryᴰ N ℓE ℓE')
         (G : StrongMonoidalFunctor M N)
  where
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module P = MonoidalCategoryᴰ P
    module PR = HomᴰReasoning P.Cᴰ
    module G = StrongMonoidalFunctor G

  -- TODO: could just require isoLifts for ε/μ
  module _ (hasPropHomsP : hasPropHoms P.Cᴰ)
           (isoLift : isWeakIsoFibration P.Cᴰ)
    where
    open WeakIsoLift

    reindex : MonoidalCategoryᴰ M ℓE ℓE'
    reindex .MonoidalCategoryᴰ.Cᴰ = Reindex.reindex P.Cᴰ G.F
    reindex .MonoidalCategoryᴰ.monstrᴰ =
      TensorPropᴰ→TensorStrᴰ M (Reindex.reindex P.Cᴰ G.F) hasPropHomsCᴰ MP
      where
        open TensorStrᴰ
        open MonoidalPropᴰ
        hasPropHomsCᴰ = hasPropHomsReindex P.Cᴰ G.F hasPropHomsP
        MP : MonoidalPropᴰ M (Reindex.reindex P.Cᴰ G.F)
        MP .tenstrᴰ .unitᴰ = isoLift P.unitᴰ (invIso G.ε-Iso) .f*cᴰ
        MP .tenstrᴰ .─⊗ᴰ─ = mkPropHomsFunctor hasPropHomsCᴰ
          (λ { (p , q) → isoLift (p P.⊗ᴰ q) (invIso (NatIsoAt G.μ-Iso _)) .f*cᴰ
            })
          λ { {f , g}(fᴰ , gᴰ) →
            PR.reind (cong₂ N._⋆_ refl (G.μ .N-hom _) ∙ sym (N.⋆Assoc _ _ _)
              ∙ cong₂ N._⋆_ (G.μ-isIso _ .sec) refl ∙ N.⋆IdL _)
            (isoLift _ _ .π P.⋆ᴰ ((fᴰ P.⊗ₕᴰ gᴰ) P.⋆ᴰ isoLift _ _ .σ)) }
        MP .αᴰ⟨_,_,_⟩ p q r = PR.reind
          (cong₂ N._⋆_ refl
            (cong₂ N._⋆_ refl (sym (N.⋆Assoc _ _ _) ∙ (G.αμ-law _ _ _)))
          ∙ sym (N.⋆Assoc _ _ _) ∙ sym (N.⋆Assoc _ _ _)
          ∙ cong₂ N._⋆_
             (N.⋆Assoc _ _ _
             ∙ cong₂ N._⋆_ refl
               (sym (N.⋆Assoc _ _ _)
               ∙ cong₂ N._⋆_
                 (F-Iso {F = N.─⊗─}
                   (CatIso× N.C N.C idCatIso (NatIsoAt G.μ-Iso _))
                   .snd .sec)
                 refl
               ∙ N.⋆IdL _)
             ∙ G.μ-isIso _ .sec)
             refl
          ∙ N.⋆IdL _
          )
          (isoLift _ _ .π
          P.⋆ᴰ (P.idᴰ P.⊗ₕᴰ isoLift _ _ .π)
          P.⋆ᴰ P.αᴰ⟨ p , q , r ⟩
          P.⋆ᴰ (isoLift _ (invIso (NatIsoAt G.μ-Iso _)) .σ P.⊗ₕᴰ P.idᴰ)
          P.⋆ᴰ isoLift _ (invIso (NatIsoAt G.μ-Iso _)) .σ)
        MP .α⁻¹ᴰ⟨_,_,_⟩ p q r = PR.reind
          (⋆CancelR (F-Iso {F = G.F} (NatIsoAt M.α _))
            ((N.⋆Assoc _ _ _)
            ∙ cong₂ N._⋆_ refl
              (N.⋆Assoc _ _ _
              ∙ cong₂ N._⋆_ refl
                (N.⋆Assoc _ _ _
                ∙ cong₂ N._⋆_ refl (sym (G.αμ-law _ _ _))
                ∙ sym (N.⋆Assoc _ _ _)
                ∙ cong₂ N._⋆_
                  (sym (N.⋆Assoc _ _ _) ∙ cong₂ N._⋆_ (N.α .nIso _ .sec) refl
                  ∙ N.⋆IdL _)
                  refl)
              ∙ sym (N.⋆Assoc _ _ _)
              ∙ cong₂ N._⋆_
                  (F-Iso {F = N.─⊗─}
                    (CatIso× N.C N.C (NatIsoAt G.μ-Iso _) idCatIso) .snd .sec)
                  refl
              ∙ N.⋆IdL _)
            ∙ G.μ-isIso _ .sec
            ∙ sym ((F-Iso {F = G.F} (NatIsoAt M.α _)) .snd .sec)))
          (isoLift _ _ .π
          P.⋆ᴰ (isoLift _ _ .π P.⊗ₕᴰ P.idᴰ)
          P.⋆ᴰ P.α⁻¹ᴰ⟨ p , q , r ⟩
          P.⋆ᴰ (P.idᴰ P.⊗ₕᴰ isoLift _ _ .σ)
          P.⋆ᴰ isoLift _ _ .σ
          )
        MP .ηᴰ⟨_⟩ p = PR.reind
          (cong₂ N._⋆_ refl
            (cong₂ N._⋆_ refl (sym (G.ηε-law _))
            ∙ sym (N.⋆Assoc _ _ _)
            ∙ cong₂ N._⋆_
              (sym (N.⋆Assoc _ _ _)
              ∙ cong₂ N._⋆_
                (F-Iso {F = N.─⊗─} (CatIso× N.C N.C G.ε-Iso idCatIso) .snd .sec)
                refl
              ∙ N.⋆IdL _)
              refl)
          ∙ sym (N.⋆Assoc _ _ _)
          ∙ cong₂ N._⋆_ (NatIsoAt G.μ-Iso _ .snd .sec) refl
          ∙ N.⋆IdL _)
          (isoLift _ _ .π P.⋆ᴰ ((isoLift _ _ .π P.⊗ₕᴰ P.idᴰ) P.⋆ᴰ P.ηᴰ⟨ _ ⟩))
        MP .η⁻¹ᴰ⟨_⟩ p = PR.reind
          (G.η⁻ε-law _)
          ((P.η⁻¹ᴰ⟨ _ ⟩ P.⋆ᴰ (isoLift _ _ .σ P.⊗ₕᴰ P.idᴰ)) P.⋆ᴰ isoLift _ _ .σ)
        MP .ρᴰ⟨_⟩ p = PR.reind
          (cong₂ N._⋆_ refl
          (cong₂ N._⋆_ refl (sym (G.ρε-law _))
          ∙ sym (N.⋆Assoc _ _ _)
          ∙ cong₂ N._⋆_
            (sym (N.⋆Assoc _ _ _)
            ∙ cong₂ N._⋆_
              (F-Iso {F = N.─⊗─} (CatIso× N.C N.C idCatIso G.ε-Iso) .snd .sec)
              refl
            ∙ N.⋆IdL _)
            refl)
          ∙ sym (N.⋆Assoc _ _ _)
          ∙ cong₂ N._⋆_ (G.μ-isIso _ .sec) refl
          ∙ N.⋆IdL _)
          (isoLift _ _ .π
          P.⋆ᴰ (P.idᴰ P.⊗ₕᴰ isoLift _ _ .π)
          P.⋆ᴰ P.ρᴰ⟨ p ⟩)
        MP .ρ⁻¹ᴰ⟨_⟩ p = PR.reind
          (⋆CancelR (F-Iso {F = G.F} (NatIsoAt M.ρ _))
            (N.⋆Assoc _ _ _ ∙ cong₂ N._⋆_ refl (G.ρε-law _)
            ∙ N.ρ .nIso _ .sec
            ∙ sym (F-Iso {F = G.F} (NatIsoAt M.ρ _) .snd .sec)
            ))
          (P.ρ⁻¹ᴰ⟨ p ⟩
            P.⋆ᴰ (P.idᴰ P.⊗ₕᴰ isoLift _ _ .σ)
            P.⋆ᴰ isoLift _ _ .σ)
