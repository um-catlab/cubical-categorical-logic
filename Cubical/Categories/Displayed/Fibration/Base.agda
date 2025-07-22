{-# OPTIONS --safe --lossy-unification #-}
{- This file takes 20s to type check -}
module Cubical.Categories.Displayed.Fibration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.NaturalTransformation
-- open import Cubical.Categories.Constructions.Fiber
-- open import Cubical.Categories.Presheaf.Representable
-- open import Cubical.Categories.Adjoint.UniversalElements
-- open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Instances.Sets.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Functor.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.Weaken.Base
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.FunctorComprehension

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functorᴰ
open NatTransᴰ

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module R = HomᴰReasoning Cᴰ
    module Cᴰ = Categoryᴰ Cᴰ
    module C = Category C
  {- Definition #1: Manual, what you would expect -}
  record CartesianLift {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
         : Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-max ℓCᴰ ℓCᴰ'))
         where
    field
      f*yᴰ : Cᴰ.ob[ x ]
      π : Cᴰ [ f ][ f*yᴰ , yᴰ ]
      isCartesian : ∀ {z} {zᴰ} {g : C [ z , x ]} →
        isIso λ (gᴰ : Cᴰ [ g ][ zᴰ , f*yᴰ ]) → (gᴰ Cᴰ.⋆ᴰ π)

  isFibration : Type _
  isFibration =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianLift cᴰ' f

  -- Definition #2: Semi-manual, but defined as a UniversalElementⱽ -
  -- CartesianLift' is not definitionally equivalent to CartesianLift
  -- because π is over C.id ⋆ f rather than f
  CartesianLiftPsh : ∀ {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
    → Presheafⱽ Cᴰ x ℓCᴰ'
  CartesianLiftPsh {x} {y} yᴰ f .F-obᴰ zᴰ g .fst = Cᴰ [ g C.⋆ f ][ zᴰ , yᴰ ]
  CartesianLiftPsh {x} {y} yᴰ f .F-obᴰ zᴰ g .snd = Cᴰ.isSetHomᴰ
  CartesianLiftPsh {x} {y} yᴰ f .F-homᴰ gᴰ h hfᴰ =
    R.reind (sym $ C.⋆Assoc _ _ _) $ gᴰ Cᴰ.⋆ᴰ hfᴰ
  CartesianLiftPsh {x} {y} yᴰ f .F-idᴰ = funExt λ g → funExt λ gᴰ →
    R.rectify $ R.≡out $
      sym (R.reind-filler _ _)
      ∙ R.⋆IdL _
  CartesianLiftPsh {x} {y} yᴰ f .F-seqᴰ fᴰ gᴰ = funExt λ h → funExt λ hᴰ →
    R.rectify $ R.≡out $
      (sym $ R.reind-filler _ _)
      ∙ R.⋆Assoc _ _ _
      ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
      ∙ R.reind-filler _ _
  CARTESIANLIFT : Profunctorⱽ (C /C Cᴰ) Cᴰ ℓCᴰ'
  CARTESIANLIFT .F-obᴰ (y , yᴰ , f) = CartesianLiftPsh yᴰ f
  CARTESIANLIFT .F-homᴰ (g , gᴰ , square) .N-obᴰ xᴰ h hᴰ =
    R.reind
      (C.⋆Assoc _ _ _
      ∙ C.⟨ refl ⟩⋆⟨ sym square ⟩
      ∙ sym (C.⋆Assoc _ _ _))
      $ hᴰ Cᴰ.⋆ᴰ gᴰ
  CARTESIANLIFT .F-homᴰ (g , gᴰ , square) .N-homᴰ fᴰ =
    funExt λ h → funExt λ hkᴰ →
    R.rectify $ R.≡out $
    (sym $ R.reind-filler _ _)
    ∙ R.⟨ sym $ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
    ∙ R.⋆Assoc _ _ _
    ∙ R.⟨ refl ⟩⋆⟨ R.reind-filler _ _ ⟩
    ∙ R.reind-filler _ _
  CARTESIANLIFT .F-idᴰ = makeNatTransPathᴰ (Cᴰ ^opᴰ) (SETᴰ ℓC' ℓCᴰ')
    (makeNatTransPath (funExt λ _ → funExt C.⋆IdR))
    (implicitFunExt $ funExt λ yᴰ → funExt λ f → funExt λ fgᴰ →
      R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ R.⋆IdR _)
  CARTESIANLIFT .F-seqᴰ (f , fᴰ , sq-f) (g , gᴰ , sq-g) = makeNatTransPathᴰ _ _
    (makeNatTransPath $ funExt λ _ → funExt λ h → sym $ C.⋆Assoc _ _ _)
    (implicitFunExt $ funExt λ yᴰ → funExt λ h → funExt λ hkᴰ →
      R.rectify $ R.≡out $
        (sym $ R.reind-filler _ _)
        ∙ (sym $ R.⋆Assoc _ _ _)
        ∙ R.⟨ R.reind-filler _ _ ⟩⋆⟨ refl ⟩
        ∙ R.reind-filler _ _)

  CartesianLift' : {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift' {x} yᴰ f =
    UniversalElementⱽ Cᴰ x (CARTESIANLIFT .F-obᴰ $ _ , yᴰ , f)

  isFibration' : Type _
  isFibration' =
    ∀ {c : C .ob}{c' : C .ob}
    (cᴰ' : Cᴰ.ob[ c' ])(f : C [ c , c' ])
    → CartesianLift' cᴰ' f

  CartesianLift'F : isFibration' → Functorⱽ (C /C Cᴰ) Cᴰ
  CartesianLift'F cL's = FunctorⱽComprehension {Pᴰ = CARTESIANLIFT}
    λ x (_ , yᴰ , f) → cL's yᴰ f

  module _ {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ])
    (cL : CartesianLift' yᴰ f) where
    private
      module f*yᴰ = PresheafⱽNotation (CartesianLiftPsh yᴰ f)
      module cL = UniversalElementⱽNotation Cᴰ _ _ cL
    -- This is *not* slow to typecheck, unlike the definition below. Interesting
    -- CartesianLift'→CartesianLift : CartesianLift yᴰ f
    -- CartesianLift'→CartesianLift .CartesianLift.f*yᴰ = cL.vertexⱽ
    -- -- Herein lies the rub
    -- -- Goal: Cᴰ.Hom[ f ][ cL.vertexⱽ , yᴰ ]
    -- -- cL.elementⱽ : Cᴰ.Hom[ C.id C.⋆ f ][ cL.vertexⱽ , yᴰ ]
    -- CartesianLift'→CartesianLift .CartesianLift.π = R.reind (C.⋆IdL f) cL.elementⱽ
    -- CartesianLift'→CartesianLift .CartesianLift.isCartesian .fst = cL.introᴰ _
    -- CartesianLift'→CartesianLift .CartesianLift.isCartesian .snd .fst gfᴰ =
    --   R.rectify $ R.≡out $
    --   R.⟨ refl ⟩⋆⟨ sym $ R.reind-filler _ _ ⟩
    --   ∙ (R.reind-filler _ _)
    --   ∙ (R.≡in $ cL.βᴰ)
    -- CartesianLift'→CartesianLift .CartesianLift.isCartesian .snd .snd gᴰ = ?
      -- TODO: finish this
      -- R.rectify $ R.≡out $
      -- {!cL.intro⟨_⟩!}
      -- ∙ cL.∫ue.intro⟨ {!!} ⟩
      -- ∙ (sym $ R.≡in $ cL.ηᴰ)

  -- CartesianLiftF : isFibration → Functorⱽ (C /C Cᴰ) Cᴰ
  -- CartesianLiftF cartesianLifts = {!FunctorⱽComprehension!}

  -- Definition #3: This is the "textbook" compositional
  -- definition. It suffers from very slow performance
  CartesianLift'' : {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) → Type _
  CartesianLift'' yᴰ f = RightAdjointAtⱽ (Δ/C C Cᴰ) (_ , yᴰ , f)
  -- Unfortunately the following is *extremely* slow to type check

  module _ {x y : C .ob}(yᴰ : Cᴰ.ob[ y ]) (f : C [ x , y ]) (cL : CartesianLift'' yᴰ f) where
    private
      module cL = UniversalElementⱽNotation {C = C} Cᴰ _ _ cL
    CartesianLift''→CartesianLift' : CartesianLift' yᴰ f
    CartesianLift''→CartesianLift' .UniversalElementⱽ.vertexⱽ = cL.vertexⱽ
    CartesianLift''→CartesianLift' .UniversalElementⱽ.elementⱽ = elt -- cL.elementⱽ
      where

      -- To get around normalization issues for {! cL.elementⱽ !},
      -- I first defined cle : t below with t = ?,
      -- and then I solved for the definition of t to get agda to tell me the type of cL.elementⱽ

      t : Type _
      -- Used the below normalized types and changed the names/added imports to make each module a valid name
      t = Σ (C [ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .fst , y ])
          (λ fᴰ → (Slice.reindex C Cᴰ [ C.id , fᴰ ][ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .snd .fst , yᴰ ]) ×
                   (Arrow C [ C.id , fᴰ ][ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .snd .snd , f ]))

      -- From C-u C-c C-s/C-u C-u C-c C-s
      -- t = {!Σ (C [ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .fst , y ])
      --      (λ fᴰ →
      --         (Cubical.Categories.Displayed.Constructions.Slice.Cᴰ' C Cᴰ [
      --          C.id , fᴰ ][ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .snd .fst , yᴰ ])
      --         ×
      --         (Cubical.Categories.Displayed.Instances.Arrow.Base.Arrow C [
      --          C.id , fᴰ ][ F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .snd .snd , f ]))
      --          !}

      -- From C-c C-s
      -- t = {!Σ
      --      (Categoryᴰ.Hom[
      --       Cubical.Categories.Displayed.Constructions.Weaken.Base.weaken C C
      --       ][ C.id , F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .fst ]
      --       y)
      --      (λ fᴰ →
      --         Categoryᴰ.Hom[
      --         Cubical.Categories.Displayed.Constructions.Slice.Cᴰ' C Cᴰ
      --         Cubical.Categories.Displayed.BinProduct._.×ᴰ
      --         Cubical.Categories.Displayed.Instances.Arrow.Base.Arrow C
      --         ][ C.id , fᴰ , F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ .snd ]
      --         (yᴰ , f))!}

      cle : t
      cle = cL.elementⱽ

      -- Defined this term with a hole for the type then solved
      fobd : Categoryᴰ.ob[ (C /C Cᴰ) ^opᴰ ] x
      fobd = F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ

      fobd' : Σ[ z ∈ C.ob ] Categoryᴰ.ob[ Cᴰ ] z × C [ x , z ]
      fobd' = F-obᴰ (Δ/C C Cᴰ ^opFⱽ) cL.vertexⱽ

      x' : C.ob
      x' = fobd .fst

      _ : x ≡ x'
      _ = refl -- nice

      x→x : C [ x , x ]
      x→x = fobd .snd .snd

      _ : x→x ≡ C.id
      _ = refl

      xᴰ : Categoryᴰ.ob[ Cᴰ ] x
      xᴰ = fobd .snd .fst

      t' : Type _
      t' = Σ[ h ∈ C [ x , y ] ] ((Cᴰ [ h ][ xᴰ , yᴰ ]) × (C.id ⋆⟨ C ⟩ f ≡ C.id ⋆⟨ C ⟩ h))

      --              h
      --    x ---------------> y
      --    ^                  ^
      --    |                  |
      -- id |                  | f
      --    |                  |
      --    x ---------------> x
      --             id

      cle' : t'
      cle' = cL.elementⱽ

      h = cle .fst
      hᴰ = cle .snd .fst
      id-f≡id-h = cle .snd .snd

      -- Goal needs a morphism displayed over id ⋆⟨ C ⟩ f
      p : C.id ⋆⟨ C ⟩ f ≡ h
      p = id-f≡id-h ∙ C.⋆IdL h

      elt : Cᴰ [ C.id ⋆⟨ C ⟩ f ][ xᴰ , yᴰ ]
      elt = subst (λ z → Cᴰ [ z ][ xᴰ , yᴰ ]) (sym p) hᴰ
      -- This is actually pretty simple once you know what's going on
      -- On Friday we sketched this out manually but here Agda kinda gives us the right type
      --
      -- C-u C-u C-c C-. Annoyingly hangs but the above method gets us
      -- Agda to tell us the defintion of the type

    -- TODO
    CartesianLift''→CartesianLift' .UniversalElementⱽ.universalⱽ {y = z} {yᴰ = zᴰ} {f = g} = {!!}
      -- {!equivToIso (_ , (cL.universal ?))!}
    -- CartesianLift''→CartesianLift' .UniversalElementⱽ.universalⱽ {y = z} {yᴰ = zᴰ} {f = g} .fst gᴰ = {!cL.element!}
    -- CartesianLift''→CartesianLift' .UniversalElementⱽ.universalⱽ .snd .fst b = {!!}
    -- CartesianLift''→CartesianLift' .UniversalElementⱽ.universalⱽ .snd .snd = {!!}

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
