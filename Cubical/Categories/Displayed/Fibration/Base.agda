{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Constructions.Fiber
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

  record CartesianLift {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
         where
    field
      f*yᴰ : Cᴰ.ob[ x ]
      π : Cᴰ [ f ][ f*yᴰ , yᴰ ]
      isCartesian : ∀ {z} {zᴰ} {g : C [ z , x ]} →
        isIso λ (gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]) → (gᴰ Cᴰ.⋆ᴰ π)
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

  isFibration : Type _
  isFibration =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianLift cᴰ' f
-- module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
--   {F : Functor C D}
--   {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
--   where
--   private
--     module Cᴰ = Categoryᴰ Cᴰ
--   PreservesCartesianLifts : Functorᴰ F Cᴰ Dᴰ → Type _
--   PreservesCartesianLifts Fᴰ =
--       ∀ {c c' : C .ob} (c'ᴰ : Cᴰ.ob[ c' ]) (f : C [ c , c' ]) →
--       (f*c'ᴰ : Cᴰ.ob[ c ])(fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) →
--         isCartesianOver Cᴰ c'ᴰ f fᴰ →
--         isCartesianOver Dᴰ (Fᴰ .F-obᴰ c'ᴰ) (F ⟪ f ⟫) (Fᴰ .F-homᴰ fᴰ)


-- -- -- package together a fibration and its cleavage, with an explicit base
-- -- ClovenFibration : (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level) → Type _
-- -- ClovenFibration C ℓCᴰ ℓCᴰ' = Σ[ Cᴰ ∈ Categoryᴰ C ℓCᴰ ℓCᴰ' ] isFibration Cᴰ

-- -- module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
-- --   (p : ClovenFibration C ℓCᴰ ℓCᴰ')(q : ClovenFibration D ℓDᴰ ℓDᴰ') where
-- --   module _ {F : Functor C D} (Fᴰ : Functorᴰ F (p .fst) (q .fst)) where
-- --     open Category
-- --     open Functorᴰ
-- --     private
-- --       module Cᴰ = Categoryᴰ (p .fst)

-- --   record FiberedFunctor
-- --       : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓD ℓD'))
-- --       (ℓ-max (ℓ-max ℓCᴰ ℓCᴰ') (ℓ-max ℓDᴰ ℓDᴰ'))) where
-- --     field
-- --       base : Functor C D
-- --       over : Functorᴰ base (p .fst) (q .fst)
-- --       preserves-cartesian : PreservesCartesianLifts (p .snd) (q .snd) over
