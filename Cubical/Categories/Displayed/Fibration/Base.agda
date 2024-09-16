{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Functor

open import Cubical.Tactics.CategorySolver.Reflection

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functorᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    C/Cᴰ = (C /C Cᴰ)
    module C/Cᴰ = Categoryᴰ C/Cᴰ
    Δ = Δ/C C Cᴰ
  -- The "high tech" formulation
  CartesianLift : ∀ {c : C .ob} → C/Cᴰ.ob[ c ] → Type _
  CartesianLift = VerticalRightAdjointAtᴰ Δ

  isFibration : Type _
  isFibration = VerticalRightAdjointᴰ Δ

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

  module _ {c c' : C .ob}(c'ᴰ : Cᴰ.ob[ c' ])(f : C [ c , c' ]) where
    -- type of witnesses that fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ] is cartesian,
    -- for convenience
    isCartesianOver : ∀{f*c'ᴰ : Cᴰ.ob[ c ]} →
      (fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) → Type _
    isCartesianOver {f*c'ᴰ = f*c'ᴰ} fᴰ =
      ∀ {c'' : C .ob}(c''ᴰ : Cᴰ.ob[ c'' ])(g : C [ c'' , c ])
      (gfᴰ : Cᴰ.Hom[ g ⋆⟨ C ⟩ f ][ c''ᴰ , c'ᴰ ]) →
      ∃![ gᴰ ∈ Cᴰ.Hom[ g ][ c''ᴰ , f*c'ᴰ ] ] (gᴰ Cᴰ.⋆ᴰ fᴰ ≡ gfᴰ)

    open CartesianOver

    isCartesianOver→CartesianOver :
      {f*c'ᴰ : Cᴰ.ob[ c ]}{fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]} →
      isCartesianOver fᴰ → CartesianOver c'ᴰ f
    isCartesianOver→CartesianOver {f*c'ᴰ = f*c'ᴰ} _ .f*cᴰ' = f*c'ᴰ
    isCartesianOver→CartesianOver {fᴰ = fᴰ} _ .π = fᴰ
    isCartesianOver→CartesianOver !gᴰ .isCartesian = !gᴰ

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
          (symP (R.rectify (R.≡out (R.reind-filler _ _ ∙ R.≡in (sym β))))))))
        (λ _ → C/Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ-lifts →
        cong fst (isCL .snd (gᴰ
                   , sym (fromPathP (symP (cong (λ p → p .snd .fst) gᴰ-lifts)))
          ∙ R.rectify (R.≡out (sym (R.reind-filler _ _) ∙ R.reind-filler _ _))))
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
        (R.rectify (R.≡out (R.⟨ refl ⟩⋆⟨ symP (R.reind-filler f'≡f π') ⟩ ∙
          R.≡in (λ i → the-CL .fst .snd i .snd .fst))))
        (λ _ → Cᴰ.isSetHomᴰ _ _)
        λ gᴰ gᴰ⋆π≡gfᴰ → cong fst (the-CL .snd (gᴰ ,
          ΣPathP (g⋆f'≡g⋆f , (ΣPathPProp (λ _ → C .isSetHom _ _)
          (R.rectify (R.≡out (R.⟨ refl ⟩⋆⟨ R.reind-filler f'≡f π' ⟩ ∙
            R.≡in (gᴰ⋆π≡gfᴰ))))))))
      where
        the-CL = cL.universalᴰ .equiv-proof (g ⋆⟨ C ⟩ f , gfᴰ , solveCat! C)
        ⟨gfᴰ⟩ : Cᴰ.Hom[ g ][ cᴰ'' , cL.vertexᴰ ]
        ⟨gfᴰ⟩ = the-CL .fst .fst

        g⋆f'≡g⋆f : g ⋆⟨ C ⟩ f' ≡ g ⋆⟨ C ⟩ f
        g⋆f'≡g⋆f = cong fst (the-CL .fst .snd)

        gᴰ⋆π'≡gᴰ⋆π : ∀ (gᴰ : Cᴰ.Hom[ g ][ cᴰ'' , f'*cᴰ' ])
                   → gᴰ Cᴰ.⋆ᴰ π' Cᴰ.≡[ cong (seq' C g) f'≡f ] (gᴰ Cᴰ.⋆ᴰ the-π)
        gᴰ⋆π'≡gᴰ⋆π gᴰ =
          R.rectify (R.≡out (R.⟨ refl ⟩⋆⟨ R.reind-filler f'≡f π' ⟩))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  PreservesCartesianLifts : Functorᴰ F Cᴰ Dᴰ → Type _
  PreservesCartesianLifts Fᴰ =
      ∀ {c c' : C .ob} (c'ᴰ : Cᴰ.ob[ c' ]) (f : C [ c , c' ]) →
      (f*c'ᴰ : Cᴰ.ob[ c ])(fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) →
        isCartesianOver Cᴰ c'ᴰ f fᴰ →
        isCartesianOver Dᴰ (Fᴰ .F-obᴰ c'ᴰ) (F ⟪ f ⟫) (Fᴰ .F-homᴰ fᴰ)

-- -- package together a fibration and its cleavage, with an explicit base
-- ClovenFibration : (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
-- ClovenFibration C ℓCᴰ ℓCᴰ' = Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ] isFibration Cᴰ

-- module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
--   (p : ClovenFibration C ℓCᴰ ℓCᴰ')(q : ClovenFibration D ℓDᴰ ℓDᴰ') where
--   module _ {F : Functor C D} (Fᴰ : Functorᴰ F (p .fst) (q .fst)) where
--     open Category
--     open Functorᴰ
--     private
--       module Cᴰ = Categoryᴰ (p .fst)

--   record FiberedFunctor
--       : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
--       (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
--     field
--       base : Functor C D
--       over : Functorᴰ base (p .fst) (q .fst)
--       preserves-cartesian : PreservesCartesianLifts (p .snd) (q .snd) over
