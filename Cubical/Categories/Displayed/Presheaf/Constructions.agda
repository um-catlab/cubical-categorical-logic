{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Presheaf.Constructions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Bifunctor.Redundant

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open Functor
open Functorᴰ
open isIsoOver

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
  PshProdᴰ : {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
             (Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ) (Qᴰ : Presheafᴰ Cᴰ Q ℓQᴰ)
           → Presheafᴰ Cᴰ (PshProd ⟅ P , Q ⟆b) (ℓ-max ℓPᴰ ℓQᴰ)
  PshProdᴰ Pᴰ Qᴰ .F-obᴰ xᴰ (p , q) .fst =
    ⟨ Pᴰ .F-obᴰ xᴰ p ⟩ × ⟨ Qᴰ .F-obᴰ xᴰ q ⟩
  PshProdᴰ Pᴰ Qᴰ .F-obᴰ xᴰ (p , q) .snd =
    isSet× (Pᴰ .F-obᴰ xᴰ p .snd) (Qᴰ .F-obᴰ xᴰ q .snd)
  PshProdᴰ Pᴰ Qᴰ .F-homᴰ fᴰ (p , q) (pᴰ , qᴰ) .fst = Pᴰ .F-homᴰ fᴰ p pᴰ
  PshProdᴰ Pᴰ Qᴰ .F-homᴰ fᴰ (p , q) (pᴰ , qᴰ) .snd = Qᴰ .F-homᴰ fᴰ q qᴰ
  PshProdᴰ Pᴰ Qᴰ .F-idᴰ = funExt (λ (p , q) → funExt λ (pᴰ , qᴰ) →
    ΣPathP ( funExt⁻ (funExt⁻ (Pᴰ .F-idᴰ) p) pᴰ
           , (funExt⁻ (funExt⁻ (Qᴰ .F-idᴰ) q) qᴰ)))
  PshProdᴰ Pᴰ Qᴰ .F-seqᴰ fᴰ gᴰ =
     funExt (λ (p , q) → funExt λ (pᴰ , qᴰ) → ΣPathP
       ( (funExt⁻ (funExt⁻ (Pᴰ .F-seqᴰ fᴰ gᴰ) p) pᴰ)
       , (funExt⁻ (funExt⁻ (Qᴰ .F-seqᴰ fᴰ gᴰ) q) qᴰ)))


open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ Cᴰ P ℓPᴰ} {Qᴰ : Presheafᴰ Cᴰ Q ℓQᴰ}
  (P×Q : UniversalElement C (P ×𝓟 Q))
  (lift-π₁ : CartesianLift (P×Q .element .fst) Pᴰ)
  (lift-π₂ : CartesianLift (P×Q .element .snd) Qᴰ)
  (bpⱽ : BinProductⱽ Cᴰ (lift-π₁ .p*Pᴰ , lift-π₂ .p*Pᴰ))
  where
  open BinProductⱽNotation bpⱽ

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module R = HomᴰReasoning Cᴰ
    module Pᴰ = PresheafᴰReasoning Pᴰ
    module Qᴰ = PresheafᴰReasoning Qᴰ
    module P×Q = UniversalElementNotation P×Q
  BinProductⱽ→UnivPshProdᴰ : UniversalElementᴰ Cᴰ (PshProdᴰ Pᴰ Qᴰ) P×Q
  BinProductⱽ→UnivPshProdᴰ .vertexᴰ = vert
  BinProductⱽ→UnivPshProdᴰ .elementᴰ .fst = π₁ Pᴰ.⋆ⱽᴰ lift-π₁ .π
  BinProductⱽ→UnivPshProdᴰ .elementᴰ .snd = π₂ Qᴰ.⋆ⱽᴰ lift-π₂ .π
  BinProductⱽ→UnivPshProdᴰ .universalᴰ .inv (p , q) (pᴰ , qᴰ) =
    lift-π₁ .isCartesian .fst (Pᴰ.reind (sym (cong fst P×Q.β)) pᴰ) ,ⱽ
    lift-π₂ .isCartesian .fst (Qᴰ.reind (sym (cong snd P×Q.β)) qᴰ)
  BinProductⱽ→UnivPshProdᴰ .universalᴰ .rightInv (p , q) (pᴰ , qᴰ) = ΣPathP
    ( (Pᴰ.rectify $ Pᴰ.≡out $
      (sym $ Pᴰ.≡in $ Pᴰ.⋆Assocᴰⱽᴰ _ _ _)
      ∙ Pᴰ.⟨ R.≡in ×βⱽ₁ ⟩⋆ᴾ⟨ refl ⟩
      ∙ (Pᴰ.≡in $ lift-π₁ .isCartesian .snd .fst $ Pᴰ.reind (sym $ cong fst P×Q.β) pᴰ)
      ∙ (sym $ Pᴰ.reind-filler _ _))
    , ((Qᴰ.rectify $ Qᴰ.≡out $
      (sym $ Qᴰ.≡in $ Qᴰ.⋆Assocᴰⱽᴰ _ _ _)
      ∙ Qᴰ.⟨ R.≡in ×βⱽ₂ ⟩⋆ᴾ⟨ refl ⟩
      ∙ (Qᴰ.≡in $ lift-π₂ .isCartesian .snd .fst $ Qᴰ.reind (sym $ cong snd P×Q.β) qᴰ)
      ∙ (sym $ Qᴰ.reind-filler _ _)))
    )
  BinProductⱽ→UnivPshProdᴰ .universalᴰ .leftInv pq pqᴰ = R.rectify $ R.≡out $
    (R.≡in λ i →
      (lift-π₁ .isCartesian .fst $ Pᴰ.reind (sym $ cong fst P×Q.β) $ Pᴰ.⋆Assocᴰⱽᴰ pqᴰ π₁ (lift-π₁ .π) (~ i))
      ,ⱽ ((lift-π₂ .isCartesian .fst $ Qᴰ.reind (sym $ cong snd P×Q.β) $ Qᴰ.⋆Assocᴰⱽᴰ pqᴰ π₂ (lift-π₂ .π) (~ i))))
    ∙ (R.≡in {p = sym P×Q.η} $ congP₂ (λ _ → _,ⱽ_)
        (congP (λ _ → lift-π₁ .isCartesian .fst) (Pᴰ.rectify $ Pᴰ.≡out $ sym $ Pᴰ.reind-filler (sym $ cong fst P×Q.β) _))
        (congP (λ _ → lift-π₂ .isCartesian .fst) (Qᴰ.rectify $ Qᴰ.≡out $ sym $ Qᴰ.reind-filler (sym $ cong snd P×Q.β) _)))
    ∙ (R.≡in $ congP₂ (λ _ → _,ⱽ_)
        (lift-π₁ .isCartesian .snd .snd (pqᴰ ⋆ᴰⱽ⟨ Cᴰ ⟩ π₁))
        (lift-π₂ .isCartesian .snd .snd (pqᴰ ⋆ᴰⱽ⟨ Cᴰ ⟩ π₂)))
    ∙ (sym $ R.≡in ×ηⱽ)
