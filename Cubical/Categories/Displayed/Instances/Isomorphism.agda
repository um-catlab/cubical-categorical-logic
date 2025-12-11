module Cubical.Categories.Displayed.Instances.Isomorphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.More
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.ChangeOfObjects
open import Cubical.Categories.Constructions.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.HomPropertyOver

private
  variable
    ℓ ℓ' ℓᴰ ℓᴰ' : Level

module _ {C : Category ℓ ℓ'} (Cᴰ : Categoryᴰ C ℓᴰ ℓᴰ') where
  private
    module C = CategoryNotation C
    module Cᴰ = Fibers Cᴰ

  isPropIsIsoᴰ : ∀ {x y} {f : C [ x , y ]} →
    {isIso-f : isIso C f} →
    {xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]} →
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) → isProp (isIsoᴰ Cᴰ isIso-f fᴰ)
  isPropIsIsoᴰ fᴰ p q i .isIsoᴰ.invᴰ =
    (Cᴰ.rectify $ Cᴰ.≡out $
      (sym $ Cᴰ.⋆IdL _)
      ∙ Cᴰ.⟨ sym $ Cᴰ.≡in $ q .isIsoᴰ.secᴰ  ⟩⋆⟨⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.≡in (p .isIsoᴰ.retᴰ) ⟩
      ∙ Cᴰ.⋆IdR _) i
  isPropIsIsoᴰ fᴰ p q i .isIsoᴰ.secᴰ j =
    isSet→SquareP (λ _ _ → Cᴰ.isSetHomᴰ)
      (p .isIsoᴰ.secᴰ) (q .isIsoᴰ.secᴰ)
      (Cᴰ.≡out $ Cᴰ.⟨ ΣPathP (refl , (λ k → isPropIsIsoᴰ fᴰ p q k .isIsoᴰ.invᴰ)) ⟩⋆⟨⟩)
      refl i j
  isPropIsIsoᴰ fᴰ p q i .isIsoᴰ.retᴰ j =
    isSet→SquareP (λ _ _ → Cᴰ.isSetHomᴰ)
      (p .isIsoᴰ.retᴰ) (q .isIsoᴰ.retᴰ)
      (Cᴰ.≡out $ Cᴰ.⟨⟩⋆⟨ ΣPathP (refl , (λ k → isPropIsIsoᴰ fᴰ p q k .isIsoᴰ.invᴰ)) ⟩)
      refl i j

  ISOᴰ : Categoryᴰ C.ISOC ℓᴰ ℓᴰ'
  ISOᴰ .Categoryᴰ.ob[_] = Cᴰ.ob[_]
  ISOᴰ .Categoryᴰ.Hom[_][_,_] = CatIsoᴰ Cᴰ
  ISOᴰ .Categoryᴰ.idᴰ = idᴰCatIsoᴰ Cᴰ
  ISOᴰ .Categoryᴰ._⋆ᴰ_ fᴰ gᴰ =
    (fᴰ .fst Cᴰ.⋆ᴰ gᴰ .fst) ,
    (isisoᴰ (gᴰ .snd .isIsoᴰ.invᴰ Cᴰ.⋆ᴰ fᴰ .snd .isIsoᴰ.invᴰ)
            (Cᴰ.rectify $ Cᴰ.≡out $
               Cᴰ.⋆Assoc _ _ _
               ∙ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.≡in $ fᴰ .snd .isIsoᴰ.secᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _ ⟩
               ∙ Cᴰ.≡in (gᴰ .snd .isIsoᴰ.secᴰ)
             )
            (Cᴰ.rectify $ Cᴰ.≡out $
               Cᴰ.⋆Assoc _ _ _
               ∙ Cᴰ.⟨⟩⋆⟨ (sym $ Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.≡in $ gᴰ .snd .isIsoᴰ.retᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _ ⟩
               ∙ Cᴰ.≡in (fᴰ .snd .isIsoᴰ.retᴰ)
             )
            )
  ISOᴰ .Categoryᴰ.⋆IdLᴰ fᴰ = ΣPathPProp isPropIsIsoᴰ (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdL _)
  ISOᴰ .Categoryᴰ.⋆IdRᴰ fᴰ = ΣPathPProp isPropIsIsoᴰ (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdR _)
  ISOᴰ .Categoryᴰ.⋆Assocᴰ _ _ _ = ΣPathPProp isPropIsIsoᴰ (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assoc _ _ _)
  ISOᴰ .Categoryᴰ.isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ λ _ → isProp→isSet (isPropIsIsoᴰ _)
