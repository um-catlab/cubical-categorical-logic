{-

  Definition

       D
       |
       \/
  C -> E

-}
module Cubical.Categories.Limits.Pullback.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓA ℓB ℓA' ℓB' ℓC ℓC' ℓD ℓD' ℓP ℓQ ℓR ℓS : Level

open Functor
open Iso
open PshHom
open PshIso

module _ (C : Category ℓ ℓ') where
  private
    module C = Category C
  module _ {cospan : Cospan C} (pb : Pullback C cospan) where
    open Cospan cospan
    open Pullback pb

    pullbackExtensionality : ∀ {Γ}{f g : C [ Γ , pbOb ]}
      → (f C.⋆ pbPr₁) ≡ (g C.⋆ pbPr₁)
      → (f C.⋆ pbPr₂) ≡ (g C.⋆ pbPr₂)
      → f ≡ g
    pullbackExtensionality f1≡g1 f2≡g2 = (sym $ pullbackArrowUnique {H = C.⋆Assoc _ _ _ ∙ C.⟨ refl ⟩⋆⟨ pbCommutes ⟩ ∙ sym (C.⋆Assoc _ _ _)} refl refl)
      ∙ pullbackArrowUnique f1≡g1 f2≡g2
    -- TODO: this is a natural iso proving that Yoneda preserves
    -- pullbacks.
    isPullback→ΣIso : ∀ Γ (f : C [ Γ , l ])
      → Iso (fiber (C._⋆ pbPr₁) f)
            (fiber (C._⋆ s₂) (f C.⋆ s₁))
    isPullback→ΣIso Γ f .fun (g , gπ₁≡f) = (g C.⋆ pbPr₂) ,
      C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym $ pbCommutes ⟩
      ∙ sym (C.⋆Assoc _ _ _)
      ∙ C.⟨ gπ₁≡f ⟩⋆⟨ refl ⟩
    isPullback→ΣIso Γ f .inv (h , hs₂≡fs₁) = (pullbackArrow f h (sym $ hs₂≡fs₁))
      , (sym $ pullbackArrowPr₁ C pb f h (sym $  hs₂≡fs₁))
    isPullback→ΣIso Γ f .sec (h , hs₂≡fs₁) = ΣPathPProp (λ _ → C.isSetHom _ _) $
      (sym $ pullbackArrowPr₂ C pb f h (sym $  hs₂≡fs₁))
    isPullback→ΣIso Γ f .ret (g , gπ₁≡f) = ΣPathPProp (λ _ → C.isSetHom _ _) $
      pullbackArrowUnique (sym gπ₁≡f) refl
