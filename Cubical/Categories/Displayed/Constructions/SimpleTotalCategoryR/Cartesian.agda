module Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor

open import Cubical.Categories.Displayed.Limits.Cartesian
import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
  as TotalCatᴰ
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

module _
  (C : CartesianCategory ℓC ℓC')
  (D : CartesianCategory ℓD ℓD')
  (Cᴰ : CartesianCategoryᴰ (C ×CC D) ℓCᴰ ℓCᴰ')
  where
  open UniversalElementᴰ
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
    module Cᴰ = CartesianCategoryᴰNotation Cᴰ
    --module R = HomᴰReasoning (Cᴰ .fst)
  ∫Cᴰsr : CartesianCategoryᴰ C _ _
  ∫Cᴰsr .fst = TotalCatᴰ.∫Cᴰsr {C = C .fst} {D = D .fst} (Cᴰ .fst)
  -- (lifted) terminal
  ∫Cᴰsr .snd .fst .vertexᴰ = D.𝟙 , Cᴰ.𝟙ᴰ
  ∫Cᴰsr .snd .fst .elementᴰ = _
  ∫Cᴰsr .snd .fst .universalᴰ .equiv-proof _ = uniqueExists
    (D.!t , Cᴰ.!tᴰ' _) --(D.!t , R.reind (≡-× C.𝟙η' refl) (Cᴰ.!tᴰ _))
    refl
    {!!} --(λ _ _ _ → refl)
    {!!} --(λ _ _ → ΣPathP (D.𝟙η' , R.rectify (R.≡out (sym (R.reind-filler _ _) ∙ symP (R.≡in (Cᴰ.𝟙ηᴰ _))))))
  -- (lifted) products
  ∫Cᴰsr .snd .snd {d = c , c'} ((d , cdᴰ) , d' , c'd'ᴰ) .vertexᴰ = (d D.×bp d') , (cdᴰ Cᴰ.×ᴰ c'd'ᴰ)
  ∫Cᴰsr .snd .snd {d = c , c'} ((d , cdᴰ) , d' , c'd'ᴰ) .elementᴰ = (D.π₁ , Cᴰ.π₁ᴰ) , (D.π₂ , Cᴰ.π₂ᴰ)
  ∫Cᴰsr .snd .snd {d = c , c'} ((d , cdᴰ) , d' , c'd'ᴰ) .universalᴰ {f = f} .equiv-proof (a , b) = uniqueExists
    (a .fst D.,p b .fst , Cᴰ._,pᴰ'_ ({!!} , {!!}) {!a .snd!} {!!}) --((a .fst D.,p b .fst) , R.reind (≡-× (sym C.×η) refl) (a .snd Cᴰ.,pᴰ b .snd))
    {!!} --(≡-× (ΣPathP (D.×β₁ , (R.rectify (R.≡out (goal ∙ R.≡in Cᴰ.×β₁ᴰ))))) (ΣPathP (D.×β₂ , {!!})))
    {!!}
    {!!}
    --where
    --open import Cubical.Categories.Category
    --open Category
    --goal : ((f ⋆⟨ C .fst ⟩ C.π₁ , {!!}) , {!!}) ≡ ((({!!} C.,p {!!}) ⋆⟨ C .fst ⟩ C.π₁ , {!!}) , {!!})
    --goal = {!!}
