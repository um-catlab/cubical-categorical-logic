{-# OPTIONS --safe --lossy-unification #-}
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
open import Cubical.Categories.Displayed.Reasoning

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    C/Cᴰ = (C /C (Fst {Cᴰ = Cᴰ}))
    module C/Cᴰ = Categoryᴰ C/Cᴰ
  -- The "high tech" formulation
  CartesianLift : ∀ {c : C .ob} → C/Cᴰ.ob[ c ] → Type _
  CartesianLift = LocalRightAdjointAtᴰ (cod Cᴰ)

  isFibration : Type _
  isFibration = LocalRightAdjointᴰ (cod Cᴰ)

  private
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
           {cᴰ' : Cᴰ.ob[ c' ]}{f : C [ c , c' ]}
           (cartOver : CartesianOver cᴰ' f)
           where
    open CartesianOver cartOver
    -- | ALERT: this definition does have to introduce a reind, may
    -- | likely complicate goals
    CartesianOver→CartesianLift : CartesianLift ((c' , cᴰ') , f)
    CartesianOver→CartesianLift .vertexᴰ = f*cᴰ'
    CartesianOver→CartesianLift .elementᴰ = (f , π) , refl
    CartesianOver→CartesianLift .universalᴰ {c''}{cᴰ''}{g}
      .equiv-proof ((gf , gfᴰ), p) =
      uniqueExists
        ⟨gfᴰ⟩
        (Σ≡Prop (λ _ → C .isSetHom _ _)
          (ΣPathP ((sym gf≡g⋆f) , symP (≡→≡[] Cᴰ (sym β)))))
        (λ _ → C/Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ-lifts → cong fst (isCL .snd (gᴰ ,
          sym (fromPathP (symP (cong snd (cong fst gᴰ-lifts))))
          ∙ reind-rectify Cᴰ))
      where
        gf≡g⋆f = sym (C .⋆IdL gf) ∙ p ∙ cong (comp' C f) (C .⋆IdR g)
        isCL = isCartesian cᴰ'' g (reind Cᴰ gf≡g⋆f gfᴰ)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , f*cᴰ' ]
        ⟨gfᴰ⟩ = isCL .fst .fst
        β : ⟨gfᴰ⟩ Cᴰ.⋆ᴰ π ≡ reind Cᴰ gf≡g⋆f gfᴰ
        β = isCL .fst .snd

  module _ {c : C .ob} {c' : C .ob}
           {cᴰ' : Cᴰ.ob[ c' ]}{f : C [ c , c' ]}
           (cartLift : CartesianLift ((c' , cᴰ') , f))
           where
    open CartesianOver
    module cL = UniversalElementᴰ cartLift
    private
      f' : C [ c , c' ]
      f' = cL.elementᴰ .fst .fst

      f'≡f : f' ≡ f
      f'≡f = (sym (C .⋆IdL _) ∙ cL.elementᴰ .snd ∙ C .⋆IdL f)

      f'*cᴰ' : Cᴰ.ob[ c ]
      f'*cᴰ' = cL.vertexᴰ

      π' : Cᴰ.Hom[ f' ][ f'*cᴰ' , cᴰ' ]
      π' = cL.elementᴰ .fst .snd

      the-π : Cᴰ.Hom[ f ][ f'*cᴰ' , cᴰ' ]
      the-π = reind Cᴰ f'≡f π'

    CartesianLift→CartesianOver : CartesianOver cᴰ' f
    CartesianLift→CartesianOver .f*cᴰ' = cL.vertexᴰ
    CartesianLift→CartesianOver .π     = the-π
    CartesianLift→CartesianOver .isCartesian {c''} cᴰ'' g gfᴰ =
      uniqueExists
        ⟨gfᴰ⟩
        (symP (fromPathP
          -- This looks the same as gᴰ⋆π'≡gᴰ⋆π but it isn't
          ((≡[]-rectify Cᴰ (≡[]⋆ Cᴰ refl f'≡f refl (reind-filler Cᴰ f'≡f π')))))
        ▷ fromPathP ⟨gfᴰ⟩⋆π'≡gfᴰ)
        (λ _ → Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ⋆π≡gfᴰ → cong fst (the-CL .snd (gᴰ ,
          Σ≡Prop (λ _ → C .isSetHom _ _)
          (ΣPathP (cong (seq' C g) f'≡f
          , (gᴰ⋆π'≡gᴰ⋆π gᴰ ▷ gᴰ⋆π≡gfᴰ)))))
      where
        the-CL = cL.universalᴰ .equiv-proof ((g ⋆⟨ C ⟩ f , gfᴰ) , solveCat! C)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , cL.vertexᴰ ]
        ⟨gfᴰ⟩ = the-CL .fst .fst

        g⋆f'≡g⋆f : g ⋆⟨ C ⟩ f' ≡ g ⋆⟨ C ⟩ f
        g⋆f'≡g⋆f = cong fst (cong fst (the-CL .fst .snd))

        ⟨gfᴰ⟩⋆π'≡gfᴰ : (⟨gfᴰ⟩ Cᴰ.⋆ᴰ π') Cᴰ.≡[ g⋆f'≡g⋆f ] gfᴰ
        ⟨gfᴰ⟩⋆π'≡gfᴰ = cong snd (cong fst (the-CL .fst .snd))

        gᴰ⋆π'≡gᴰ⋆π : ∀ (gᴰ : Cᴰ.Hom[ g ][ cᴰ'' , f'*cᴰ' ])
                   → gᴰ Cᴰ.⋆ᴰ π' Cᴰ.≡[ cong (seq' C g) f'≡f ] (gᴰ Cᴰ.⋆ᴰ the-π)
        gᴰ⋆π'≡gᴰ⋆π gᴰ =
          ≡[]-rectify Cᴰ (≡[]⋆ Cᴰ refl f'≡f refl (reind-filler Cᴰ f'≡f π'))
