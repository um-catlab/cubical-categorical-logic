module Cubical.Categories.LocallySmall.Presheaf.Constructions.BinProduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Presheaf.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level
open import Cubical.Categories.LocallySmall.Instances.Functor.Fibered
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
  hiding (π₁ ; π₂)
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Functor.Constant
open import Cubical.Categories.LocallySmall.NaturalTransformation.SmallFibered

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Bisection
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Total
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base
open import Cubical.Categories.LocallySmall.Displayed.Bifunctor.Base

open Category
open Categoryᴰ
open Σω
open Liftω

private
  variable
    ℓP ℓQ ℓR : Level

module _ (C : SmallCategory ℓC ℓC') where
  private
    module C = SmallCategory C
    module SET = CategoryᴰNotation SET

  open Functorᴰ
  PshProd' : Functorᴰ ℓ-MAX (PSH ×Cᴰ PSH) PSH
  PshProd' = postcomposeF _ _ ×SET ∘Fᴰ ,F-SFFunctorⱽ (C ^opsmall) SET SET

  PshProdᴰ : Bifunctorᴰ (ParFunctorToBifunctor ℓ-MAX) PSH PSH PSH
  PshProdᴰ = ParFunctorᴰToBifunctorᴰ PshProd'

  PshProd : Bifunctor PSH.∫C PSH.∫C PSH.∫C
  PshProd = Bifunctorᴰ.∫F PshProdᴰ

  open Bifunctor
  _×Psh_ : Presheaf C ℓP → Presheaf C ℓQ → Presheaf C (ℓ-max ℓP ℓQ)
  P ×Psh Q = PshProd .Bif-ob ⟨ P ⟩Psh ⟨ Q ⟩Psh .snd

  open SmallFibNatTrans
  module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
    π₁ : PSH.Hom[ ⟨ P ×Psh Q ⟩Psh , ⟨ P ⟩Psh ]
    π₁ .fst = tt
    π₁ .snd .N-ob = λ _ → fst
    π₁ .snd .N-hom f = transportRefl _

    π₂ : PSH.Hom[ ⟨ P ×Psh Q ⟩Psh , ⟨ Q ⟩Psh ]
    π₂ .fst = tt
    π₂ .snd .N-ob = λ _ → snd
    π₂ .snd .N-hom f = transportRefl _

  -- TODO
  module _
    {P : Presheaf C ℓP}
    {Q : Presheaf C ℓQ}
    {R : Presheaf C ℓR}
    (α : PSH.Hom[ ⟨ R ⟩Psh , ⟨ P ⟩Psh ])
    (β : PSH.Hom[ ⟨ R ⟩Psh , ⟨ Q ⟩Psh ])
    where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q

    ×PshIntro : PSH.Hom[ ⟨ R ⟩Psh , ⟨ P ×Psh Q ⟩Psh  ]
    ×PshIntro .fst = tt
    ×PshIntro .snd .N-ob c x = α .snd .N-ob c x , β .snd .N-ob c x
    ×PshIntro .snd .N-hom f =
      funExt λ p →
        (λ i → α .snd .N-hom f i p , β .snd .N-hom f i p)
        ∙ ΣPathP (
          (transportRefl _
           ∙ P.⟨⟩⋆⟨ sym $ transportRefl _ ⟩
           ∙ (sym $ transportRefl _)
           ∙ (sym $ transportRefl _)) ,
          transportRefl _
           ∙ Q.⟨⟩⋆⟨ sym $ transportRefl _ ⟩
           ∙ (sym $ transportRefl _)
           ∙ (sym $ transportRefl _))

    ×Pshβ₁ : ×PshIntro PSH.⋆ π₁ P Q ≡ α
    ×Pshβ₁ = makeSFNatTransPath refl (λ _ → refl)

    ×Pshβ₂ : ×PshIntro PSH.⋆ π₂ P Q ≡ β
    ×Pshβ₂ = makeSFNatTransPath refl (λ _ → refl)

  module _ (P : Presheaf C ℓP)(Q : Presheaf C ℓQ) where
    ×Psh-UMP :
      ∀ {R : Presheaf C ℓR} →
      Iso PSH.Hom[ ⟨ R ⟩Psh , ⟨ P ×Psh Q ⟩Psh ]
          (PSH.Hom[ ⟨ R ⟩Psh , ⟨ P ⟩Psh ] × PSH.Hom[ ⟨ R ⟩Psh , ⟨ Q ⟩Psh ])
    ×Psh-UMP .Iso.fun α = (α PSH.⋆ π₁ P Q) , (α PSH.⋆ π₂ P Q)
    ×Psh-UMP .Iso.inv (α , β) = ×PshIntro α β
    ×Psh-UMP .Iso.rightInv (α , β) = ΣPathP ((×Pshβ₁ α β) , (×Pshβ₂ α β))
    ×Psh-UMP .Iso.leftInv α = makeSFNatTransPath refl (λ _ → refl)
