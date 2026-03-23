module Cubical.Categories.Displayed.FixedPoint where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.FixedPoint

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex

open Category
open Functor

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  fixed-pointᴰ : ∀ {𝟙 x}{f : C [ x , x ]}
    → fixed-point C 𝟙 f
    → (𝟙ᴰ : Cᴰ.ob[ 𝟙 ])
    → {xᴰ : Cᴰ.ob[ x ]}
    → Cᴰ.Hom[ f ][ xᴰ , xᴰ ] → Type _
  fixed-pointᴰ {𝟙} {x} {f} (fix⟨f⟩ , fix⟨f⟩f≡fix⟨f⟩) 𝟙ᴰ {xᴰ} fᴰ =
    Σ[ fixᴰ⟨fᴰ⟩ ∈ Cᴰ.Hom[ fix⟨f⟩ ][ 𝟙ᴰ , xᴰ ] ]
    ((fixᴰ⟨fᴰ⟩ Cᴰ.⋆ᴰ fᴰ) Cᴰ.≡[ fix⟨f⟩f≡fix⟨f⟩ ] fixᴰ⟨fᴰ⟩)

  fixed-pointⱽ : (y : C.ob) (𝟙ⱽ : Cᴰ.ob[ y ]) {xⱽ : Cᴰ.ob[ y ]} →
                  Cᴰ.v[ y ] [ xⱽ , xⱽ ] → Type ℓCᴰ'
  fixed-pointⱽ = λ (y : C .ob) → fixed-point Cᴰ.v[ y ]

  -- Theorem: To construct a displayed fixed point it is
  -- sufficient to have a vertical fixed point for a cartesian
  -- lift of the fixed point in the base.
  module _ {𝟙 x}{f : C [ x , x ]}
      (fix⟨f⟩ : fixed-point C 𝟙 f)
      (𝟙ᴰ : Cᴰ.ob[ 𝟙 ])
      {xᴰ : Cᴰ.ob[ x ]}
      (fᴰ : Cᴰ.Hom[ f ][ xᴰ , xᴰ ])
      (fix⟨f⟩*xᴰ : CartesianLift Cᴰ (fix⟨f⟩ .fst) xᴰ) where
    private module fix⟨f⟩*xᴰ = CartesianLiftNotation Cᴰ fix⟨f⟩*xᴰ
    fixed-pointⱽ→ᴰ :
      fixed-pointⱽ 𝟙 𝟙ᴰ {xⱽ = fix⟨f⟩*xᴰ .fst}
        (fix⟨f⟩*xᴰ.introᴰ (Cᴰ.reind (C.⟨ C.⋆IdL _ ⟩⋆⟨ refl ⟩ ∙ fix⟨f⟩ .snd ∙ sym (C.⋆IdL _))
          (fix⟨f⟩*xᴰ.πⱽ Cᴰ.⋆ᴰ fᴰ )))
      → fixed-pointᴰ fix⟨f⟩ 𝟙ᴰ fᴰ
    fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .fst = Cᴰ.reind (C.⋆IdL _) $ fixⱽ⟨f⟩ .fst fix⟨f⟩*xᴰ.⋆πⱽ
    fixed-pointⱽ→ᴰ fixⱽ⟨f⟩ .snd = Cᴰ.rectifyOut
      (Cᴰ.⟨ Cᴰ.reind-filler⁻ _ ∙ refl ⟩⋆⟨⟩
      -- (fixⱽ⟨f⟩ ⋆πⱽ) ⋆ᴰ fᴰ
      ∙ (Cᴰ.⟨ fix⟨f⟩*xᴰ.⋆πⱽ≡⋆ᴰπⱽ _ ⟩⋆⟨⟩ ∙ Cᴰ.⋆Assoc _ _ _)
      -- fixⱽ⟨f⟩ ⋆ᴰ introᴰ _ ⋆πⱽ
      ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ ∙ (sym $ fix⟨f⟩*xᴰ.βᴰ _) ⟩
      ∙ sym fix⟨f⟩*xᴰ.⋆πⱽ-natural
      ∙ fix⟨f⟩*xᴰ.⟨ Cᴰ.reind-filler _ ∙ (Cᴰ.≡in $ fixⱽ⟨f⟩ .snd) ⟩⋆πⱽ
      -- fixⱽ⟨f⟩ ⋆πⱽ
      ∙ Cᴰ.reind-filler _)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ') (F : Functor C D)
  where
  private
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (reindex Dᴰ F)
  module _ {x : C.ob} {𝟙ⱽ xⱽ : Dᴰ.ob[ F ⟅ x ⟆ ]}{fⱽ : Dᴰ.v[ _ ] [ xⱽ , xⱽ ]} where
    reindexFixed-pointⱽ :
      fixed-pointⱽ Dᴰ (F ⟅ x ⟆) 𝟙ⱽ fⱽ
      → fixed-pointⱽ (reindex Dᴰ F) x 𝟙ⱽ (Dᴰ.reind (sym $ F .F-id) fⱽ)
    reindexFixed-pointⱽ fixⱽ⟨fⱽ⟩ .fst = Dᴰ.reind (sym $ F .F-id) $ fixⱽ⟨fⱽ⟩ .fst
    reindexFixed-pointⱽ fixⱽ⟨fⱽ⟩ .snd = F*Dᴰ.rectifyOut
      (F*Dᴰ.reind-filler⁻ _
      ∙ change-base {C = Dᴰ.Hom[_][ 𝟙ⱽ , xⱽ ]} (F .F-hom) D.isSetHom (C.⋆IdL _)
        (Dᴰ.reind-revealed-filler⁻ _
        ∙ Dᴰ.⟨ Dᴰ.reind-filler⁻ _ ⟩⋆⟨ Dᴰ.reind-filler⁻ _ ⟩
        ∙ Dᴰ.reind-filler _
        ∙ (Dᴰ.≡in $ fixⱽ⟨fⱽ⟩ .snd)
        ∙ Dᴰ.reind-filler _))
