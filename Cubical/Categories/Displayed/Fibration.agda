{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    C/Cᴰ = (C /C Cᴰ)
    module C/Cᴰ = Categoryᴰ C/Cᴰ
    Δ = Δ/C C Cᴰ
  -- The "high tech" formulation
  CartesianLift : ∀ {c : C .ob} → C/Cᴰ.ob[ c ] → Type _
  CartesianLift = LocalRightAdjointAtᴰ Δ

  isFibration : Type _
  isFibration = LocalRightAdjointᴰ Δ

  private
    module R = HomᴰReasoning Cᴰ
    module Cᴰ = Categoryᴰ Cᴰ
  -- The "explicit" formulation
  -- TODO: better names
  record CartesianOver {c : C .ob}{c' : C .ob}
                       (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ')) where
    field
      f*cᴰ' : Cᴰ.ob[ c ]
      π     : Cᴰ.Hom[ f ][ f*cᴰ' , cᴰ' ]
      isCartesian : ∀ {c'' : C .ob}(cᴰ'' : Cᴰ.ob[ c'' ])(g : C [ c'' , c ])
                    (gfᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ cᴰ'' , cᴰ' ])
                  → ∃![ gᴰ ∈ Cᴰ.Hom[ g ][ cᴰ'' , f*cᴰ' ] ] (gᴰ Cᴰ.⋆ᴰ π ≡ gfᴰ)

  AllCartesianOvers : Type _
  AllCartesianOvers =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianOver cᴰ' f

  open UniversalElementᴰ
  open isEquiv
  module _ {c : C .ob} {c' : C .ob}
           {f : C [ c , c' ]}{cᴰ' : Cᴰ.ob[ c' ]}
           (cartOver : CartesianOver cᴰ' f)
           where
    open CartesianOver cartOver
    -- | ALERT: this definition does have to introduce a reind, may
    -- | likely complicate goals
    CartesianOver→CartesianLift : CartesianLift (c' , (cᴰ' , f))
    CartesianOver→CartesianLift .vertexᴰ = f*cᴰ'
    CartesianOver→CartesianLift .elementᴰ = f , (π , refl)
    CartesianOver→CartesianLift .universalᴰ {c''} {cᴰ''} {g}
      .equiv-proof (gf , gfᴰ , gf≡g⋆f') =
      uniqueExists
        ⟨gfᴰ⟩
        (ΣPathP ((sym gf≡g⋆f) , (ΣPathPProp (λ _ → C .isSetHom _ _)
          (symP (R.≡→≡[] (sym β))))))
        (λ _ → C/Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ-lifts →
        cong fst (isCL .snd (gᴰ
                   , sym (fromPathP (symP (cong (λ p → p .snd .fst) gᴰ-lifts)))
          ∙ R.reind-rectify))
      where
        gf≡g⋆f = sym (C .⋆IdL gf) ∙ sym gf≡g⋆f' ∙ cong (comp' C f) (C .⋆IdR g)
        isCL = isCartesian cᴰ'' g (R.reind gf≡g⋆f gfᴰ)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , f*cᴰ' ]
        ⟨gfᴰ⟩ = isCL .fst .fst
        β : ⟨gfᴰ⟩ Cᴰ.⋆ᴰ π ≡ R.reind gf≡g⋆f gfᴰ
        β = isCL .fst .snd

  module _ {c : C .ob} {c' : C .ob}
           {cᴰ' : Cᴰ.ob[ c' ]}{f : C [ c , c' ]}
           (cartLift : CartesianLift (c' , (cᴰ' , f)))
           where
    open CartesianOver
    module cL = UniversalElementᴰ cartLift
    private
      f' : C [ c , c' ]
      f' = cL.elementᴰ .fst

      f'≡f : f' ≡ f
      f'≡f = sym (C .⋆IdL _) ∙ sym (cL.elementᴰ .snd .snd) ∙ C .⋆IdL _

      f'*cᴰ' : Cᴰ.ob[ c ]
      f'*cᴰ' = cL.vertexᴰ

      π' : Cᴰ.Hom[ f' ][ f'*cᴰ' , cᴰ' ]
      π' = cL.elementᴰ .snd .fst

      the-π : Cᴰ.Hom[ f ][ f'*cᴰ' , cᴰ' ]
      the-π = R.reind f'≡f π'

    CartesianLift→CartesianOver : CartesianOver cᴰ' f
    CartesianLift→CartesianOver .f*cᴰ' = cL.vertexᴰ
    CartesianLift→CartesianOver .π     = the-π
    CartesianLift→CartesianOver .isCartesian {c''} cᴰ'' g gfᴰ =
      uniqueExists
        ⟨gfᴰ⟩
        (R.≡[]-rectify (R.≡[]∙ _ _
          (R.≡[]⋆ refl (sym f'≡f) refl (symP (R.reind-filler f'≡f π')))
          (λ i → the-CL .fst .snd i .snd .fst)))
        (λ _ → Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ⋆π≡gfᴰ → cong fst (the-CL .snd (gᴰ ,
          ΣPathP (g⋆f'≡g⋆f , (ΣPathPProp (λ _ → C .isSetHom _ _)
          (R.≡[]-rectify (R.≡[]⋆ refl f'≡f refl (R.reind-filler f'≡f π'))
          ▷ gᴰ⋆π≡gfᴰ)))))
      where
        the-CL = cL.universalᴰ .equiv-proof (g ⋆⟨ C ⟩ f , gfᴰ , solveCat! C)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , cL.vertexᴰ ]
        ⟨gfᴰ⟩ = the-CL .fst .fst

        g⋆f'≡g⋆f : g ⋆⟨ C ⟩ f' ≡ g ⋆⟨ C ⟩ f
        g⋆f'≡g⋆f = cong fst (the-CL .fst .snd)

        gᴰ⋆π'≡gᴰ⋆π : ∀ (gᴰ : Cᴰ.Hom[ g ][ cᴰ'' , f'*cᴰ' ])
                   → gᴰ Cᴰ.⋆ᴰ π' Cᴰ.≡[ cong (seq' C g) f'≡f ] (gᴰ Cᴰ.⋆ᴰ the-π)
        gᴰ⋆π'≡gᴰ⋆π gᴰ =
          R.≡[]-rectify (R.≡[]⋆ refl f'≡f refl (R.reind-filler f'≡f π'))
