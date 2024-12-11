{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Constructions

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
import Cubical.Categories.Displayed.Fibration.Base as Fibration
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Categories.Displayed.Limits.BinProduct.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓQ ℓPᴰ ℓQᴰ : Level

open Category
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift
open Fibration.CartesianLift
open isIsoOver

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

module _ {C : Category ℓC ℓC'}{x₁ x₂ : C .ob}
  (prod : BinProduct' C (x₁ , x₂))
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module c×c' = BinProduct'Notation prod
  module _ {xᴰ₁ : Cᴰ.ob[ x₁ ]}{xᴰ₂ : Cᴰ.ob[ x₂ ]}
    (lift-π₁ : Fibration.CartesianLift Cᴰ xᴰ₁ c×c'.π₁)
    (lift-π₂ : Fibration.CartesianLift Cᴰ xᴰ₂ c×c'.π₂)
    (vbp : BinProductⱽ Cᴰ ((lift-π₁ .f*yᴰ) , (lift-π₂ .f*yᴰ)))
    where
    BinProductⱽ→BinProductᴰ : BinProductᴰ Cᴰ prod (xᴰ₁ , xᴰ₂)
    BinProductⱽ→BinProductᴰ = BinProductᴰPsh→BinProductᴰ Cᴰ
      (BinProductⱽ→UnivPshProdᴰ _
        (fibLift→PshᴰLift lift-π₁)
        (fibLift→PshᴰLift lift-π₂)
        vbp)
