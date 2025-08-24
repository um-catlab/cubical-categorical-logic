{- Various large associator combinators etc -}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Monoidal.Base
module Cubical.Categories.Monoidal.Combinators.Base
  {ℓ ℓ' : Level} (M : MonoidalCategory ℓ ℓ') where


import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.NaturalTransformation.More hiding (α)
open import Cubical.Categories.NaturalTransformation.Reind

private
  module M = MonoidalCategory M
  variable
    v w x y z x' x'' x''' x'''' x''''' : M.ob

-- The 3 is the number of ⊗s involved, not objects. This would make α α2
α2 = M.α

α3⟨_,_,_,_⟩ : ∀ w x y z →
  M.Hom[ w M.⊗ (x M.⊗ (y M.⊗ z)) , (w M.⊗ (x M.⊗ y)) M.⊗ z ]
α3⟨ w , x , y , z ⟩ = M.α⟨ w , (x M.⊗ y) , z ⟩ M.∘ (M.id M.⊗ₕ M.α⟨ x , y , z ⟩)

α3⁻¹⟨_,_,_,_⟩ : ∀ w x y z →
  M.Hom[ (w M.⊗ (x M.⊗ y)) M.⊗ z , w M.⊗ (x M.⊗ (y M.⊗ z)) ]
α3⁻¹⟨ w , x , y , z ⟩ =
  (M.id M.⊗ₕ M.α⁻¹⟨ x , y , z ⟩) M.∘ M.α⁻¹⟨ w , x M.⊗ y , z ⟩

α3 : NatIso {C = M.C ×C M.C ×C M.C ×C M.C}{D = M.C}
  (M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F (M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F M.─⊗─))))
  ((M.─⊗─ ∘F (M.─⊗─ ×F 𝟙⟨ M.C ⟩) ∘F ×C-assoc M.C M.C M.C) ∘F
    (𝟙⟨ M.C ⟩ ×F ((M.─⊗─ ×F 𝟙⟨ M.C ⟩) ∘F ×C-assoc M.C M.C M.C)))
α3 = seqNatIso ((M.─⊗─ ∘ʳⁱ NatIso× (idNatIso 𝟙⟨ M.C ⟩) M.α))
  (reindNatIso _ _ _ _ (Eq.refl , Eq.refl)
    ((M.α ∘ˡⁱ (𝟙⟨ M.C ⟩ ×F ((M.─⊗─ ×F 𝟙⟨ M.C ⟩) ∘F ×C-assoc M.C M.C M.C)))))

private
  testα3 : ∀ {w x y z}
    → α3⟨ w , x , y , z ⟩ ≡ α3 .NatIso.trans ⟦ w , x , y , z ⟧
  testα3 = refl

  testα⁻3 : ∀ {w x y z}
    → α3⁻¹⟨ w , x , y , z ⟩ ≡ α3 .NatIso.nIso (w , x , y , z) .isIso.inv
  testα⁻3 = refl

α4⟨_,_,_,_,_⟩ : ∀ v w x y z →
  M.Hom[ v M.⊗ (w M.⊗ (x M.⊗ (y M.⊗ z))) , (v M.⊗ (w M.⊗ (x M.⊗ y))) M.⊗ z ]
α4⟨ v , w , x , y , z ⟩ =
  M.α⟨ v , w M.⊗ (x M.⊗ y) , z ⟩
  M.∘ (M.id M.⊗ₕ α3⟨ w , x , y , z ⟩)

α4⁻¹⟨_,_,_,_,_⟩ : ∀ v w x y z →
  M.Hom[ (v M.⊗ (w M.⊗ (x M.⊗ y))) M.⊗ z , v M.⊗ (w M.⊗ (x M.⊗ (y M.⊗ z))) ]
α4⁻¹⟨ v , w , x , y , z ⟩ =
  M.id M.⊗ₕ α3⁻¹⟨ w , x , y , z ⟩
  M.∘ M.α⁻¹⟨ v , w M.⊗ (x M.⊗ y) , z ⟩

α4 : NatIso {C = M.C ×C M.C ×C M.C ×C M.C ×C M.C}{D = M.C}
  (M.─⊗─
  ∘F (𝟙⟨ M.C ⟩ ×F (M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F (M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F M.─⊗─))))))
  ((M.─⊗─ ∘F (M.─⊗─ ×F 𝟙⟨ M.C ⟩) ∘F ×C-assoc M.C M.C M.C) ∘F
    (𝟙⟨ M.C ⟩ ×F
     (((((M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F M.─⊗─)) ∘F ×C-assoc⁻ M.C M.C M.C) ×F
        𝟙⟨ M.C ⟩)
       ∘F ×C-assoc (M.C ×C M.C) M.C M.C)
      ∘F ×C-assoc M.C M.C (M.C ×C M.C))))
α4 = seqNatIso
  (((M.─⊗─ ∘ʳⁱ NatIso× (idNatIso 𝟙⟨ M.C ⟩) α3)))
  (reindNatIso _ _ _ _ (Eq.refl , Eq.refl)
    (M.α ∘ˡⁱ
    (𝟙⟨ M.C ⟩
    ×F ((((M.─⊗─ ∘F (𝟙⟨ M.C ⟩ ×F M.─⊗─)) ∘F ×C-assoc⁻ M.C M.C M.C ) ×F 𝟙⟨ M.C ⟩)
      ∘F ×C-assoc (M.C ×C M.C) M.C M.C
      ∘F ×C-assoc M.C M.C (M.C ×C M.C)))))
