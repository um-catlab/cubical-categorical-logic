module Cubical.Categories.Displayed.Constructions.Weaken.UncurriedProperties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

-- open Categoryᴰ
-- open UniversalElementᴰ
open UniversalElement
open isIsoOver
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  private
    module wkD = Fibers (weaken C D)

  module _ (termC : Terminal' C) (termD : Terminal' D) where
    termWeaken : Terminalᴰ (weaken C D) termC
    termWeaken .fst = termD .UniversalElement.vertex
    termWeaken .snd .fst = termD .UniversalElement.element
    termWeaken .snd .snd Γ Γᴰ .isIsoOver.inv a x = UniversalElementNotation.intro termD _
    termWeaken .snd .snd Γ Γᴰ .isIsoOver.rightInv b q = refl
    termWeaken .snd .snd Γ Γᴰ .isIsoOver.leftInv a p = sym $ UniversalElementNotation.η termD

  module _ (prodC : BinProducts C)(prodD : BinProducts D) where
    private
      module prodC = BinProductsNotation prodC
    private module B = BinProductsNotation prodD
    binprodWeaken : BinProductsᴰ (weaken C D) prodC
    binprodWeaken Aᴰ Bᴰ .fst = prodD (Aᴰ , Bᴰ) .UniversalElement.vertex
    binprodWeaken Aᴰ Bᴰ .snd .fst = prodD (Aᴰ , Bᴰ) .UniversalElement.element
    binprodWeaken Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.inv _ (g₁ , g₂) = g₁ B.,p g₂
    -- Too many reind fillers yuck
    binprodWeaken Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.rightInv _ _ =
      ΣPathP
        ( ((wkD.rectifyOut {e' = refl} $ sym (wkD.reind-filler _)) ∙ B.×β₁)
        , ((wkD.rectifyOut {e' = refl} $ sym (wkD.reind-filler _)) ∙ B.×β₂))
    binprodWeaken Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.leftInv _ _ =
      B.×ue.intro≡ Aᴰ Bᴰ (ΣPathP ((wkD.rectifyOut {e' = refl} (sym (wkD.reind-filler _)))
                               , ((wkD.rectifyOut {e' = refl} (sym (wkD.reind-filler _))))))

module _ (C : CartesianCategory ℓC ℓC') (D : CartesianCategory ℓD ℓD') where
  open CartesianCategory renaming (C to Cat)
  open CartesianCategoryᴰ
  weakenCartesianCategory : CartesianCategoryᴰ C ℓD ℓD'
  weakenCartesianCategory .Cᴰ = weaken (C .Cat) (D .Cat)
  weakenCartesianCategory .termᴰ = termWeaken (C .term) (D .term)
  weakenCartesianCategory .bpᴰ = binprodWeaken (C .bp) (D .bp)

module _ (C : CartesianClosedCategory ℓC ℓC') (D : CartesianClosedCategory ℓD ℓD') where
  private
    module C = CartesianClosedCategory C
    module D = CartesianClosedCategory D
    module wkD = Fibers (weaken C.C D.C)

  open CartesianClosedCategoryᴰ
  weakenCCC : CartesianClosedCategoryᴰ C ℓD ℓD'
  weakenCCC .CCᴰ = weakenCartesianCategory C.CC D.CC
  weakenCCC .expᴰ Aᴰ Bᴰ .fst = D.⇒ue.vertex Aᴰ Bᴰ
  weakenCCC .expᴰ Aᴰ Bᴰ .snd .fst = D.⇒ue.element Aᴰ Bᴰ
  weakenCCC .expᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .inv _ f⟨x⟩ = D.lda f⟨x⟩
  weakenCCC .expᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .rightInv f⟨x⟩C f⟨x⟩D =
    (wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _) ∙ D.⇒ue.β _ _
  weakenCCC .expᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .leftInv fC fD = D.⇒ue.intro≡ _ _ $
    wkD.rectifyOut {e' = refl} $ wkD.reind-filler⁻ _
