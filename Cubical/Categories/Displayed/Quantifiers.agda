{-# OPTIONS --allow-unsolved-metas #-}
module Cubical.Categories.Displayed.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.NaturalTransformation

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Slice as Slice
open import Cubical.Categories.Displayed.Constructions.TotalCategory as ∫ᴰ
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties
open import Cubical.Categories.Displayed.Presheaf

-- The universal/pi and existential/weak sigma type are defined as
-- left and right adjoints to a "weakening" functor
--
-- Cᴰ(x × y) → Cᴰ x
--     |        |
-- x:C , y:C → x:C

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {a : C .Category.ob}
  (bp : BinProductsWith C a)
  (isFib : isFibration Cᴰ)
  where
  private
    module bp = BinProductsWithNotation bp
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module isFib = isFibrationNotation _ isFib

  Cᴰ[-×a] : Categoryᴰ C ℓCᴰ ℓCᴰ'
  Cᴰ[-×a] = reindex Cᴰ bp.×aF

  open Functorᴰ
  weakenⱽ : Functorⱽ Cᴰ Cᴰ[-×a]
  weakenⱽ .F-obᴰ bᴰ = isFib.f*yᴰ bᴰ bp.π₁
  weakenⱽ .F-homᴰ fᴰ =
    isFib.introCL (Cᴰ.reind (sym $ bp.×β₁) (isFib.π Cᴰ.⋆ᴰ fᴰ))
  weakenⱽ .F-idᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.introCL≡ (sym (Cᴰ.reind-filler _ _)
      ∙ Cᴰ.⋆IdR _
      ∙ (sym $ Cᴰ.⋆IdL _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)
  weakenⱽ .F-seqᴰ fᴰ gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
    isFib.introCL≡
      (sym (Cᴰ.reind-filler _ _)
      ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.βCL) ⟩⋆⟨ refl ⟩
      ∙ Cᴰ.⋆Assoc _ _ _
      ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ (sym isFib.βCL) ⟩
      ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩
      )

  module _ {Γ} (pᴰ : Cᴰ.ob[ Γ bp.×a ]) where
    -- UniversalQuantifier : Type _
    -- UniversalQuantifier = RightAdjointAtⱽ weakenⱽ pᴰ
    open Functor
    open Functorᴰ
    UniversalQuantifierPshⱽ : Presheafⱽ Γ Cᴰ ℓCᴰ'
    UniversalQuantifierPshⱽ .F-obᴰ {Δ} Δᴰ γ .fst =
      Cᴰ [ bp.×aF ⟪ γ ⟫ ][ isFib.f*yᴰ Δᴰ bp.π₁ , pᴰ ]
    UniversalQuantifierPshⱽ .F-obᴰ {Δ} Δᴰ γ .snd = Cᴰ.isSetHomᴰ
    UniversalQuantifierPshⱽ .F-homᴰ {Δ} {Θ} {δ} {Δᴰ} {Θᴰ} δᴰ γ γᴰ =
      Cᴰ.reind (sym $ bp.×aF .F-seq _ _) (weakenⱽ .F-homᴰ δᴰ Cᴰ.⋆ᴰ γᴰ)
    UniversalQuantifierPshⱽ .F-idᴰ = {!!}
    UniversalQuantifierPshⱽ .F-seqᴰ = {!!}

    UniversalQuantifier : Type _
    UniversalQuantifier = UniversalElementⱽ Cᴰ Γ UniversalQuantifierPshⱽ
-- module _
--   {C : Category ℓC ℓC'}
--   {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
--   (bp : BinProducts C)
--   -- This is an overly strong assumption for the construction, we only
--   -- need pullbacks of π₁ . Not clear how to weaken it based on the current impl
--   (isFibration : isFibration Cᴰ)
--   where
--   open BinProductsNotation bp
--   private
--     bpF = (BinProductF' C bp)
--     Cᴰ[a×b] = reindex Cᴰ bpF
--     Cᴰ[a] = reindex Cᴰ (Fst C C)
--     module C = Category C
--     module Cᴰ = Fibers Cᴰ
--     module isFib = isFibrationNotation _ isFibration

--   π₁Fᴰ : Functorᴰ bpF Cᴰ[a] (C /C Cᴰ)
--   π₁Fᴰ = Slice.introF C Cᴰ
--     (Fst C C)
--     (Reindex.π Cᴰ (Fst C C))
--     π₁Nat

--   weakenᴰ : Functorᴰ bpF Cᴰ[a] Cᴰ
--   weakenᴰ = CartesianLiftF Cᴰ isFibration ∘Fⱽᴰ π₁Fᴰ


--   weakenⱽ : Functorⱽ {C = C ×C C} Cᴰ[a] Cᴰ[a×b]
--   weakenⱽ = Reindex.introF _ (reindF' _ Eq.refl Eq.refl
--     (CartesianLiftF Cᴰ isFibration ∘Fⱽᴰ π₁Fᴰ))

--   open isFibrationNotation Cᴰ isFibration
--   module _ {a b : C.ob} (pᴰ : Cᴰ.ob[ a × b ]) where
--     open Functorᴰ
  module UniversalQuantifierNotation {b}{pᴰ : Cᴰ.ob[ b bp.×a ]}
    (∀pᴰ : UniversalQuantifier pᴰ) where
    module ∀ueⱽ = UniversalElementⱽ ∀pᴰ
    open Functor
    open Functorᴰ

    open isFibrationNotation Cᴰ isFib

    vert : Cᴰ.ob[ b ]
    vert = ∀ueⱽ.vertexᴰ

    app : Cᴰ [ bp.×aF ⟪ C.id ⟫ ][ f*yᴰ vert bp.π₁ , pᴰ ]
    app = ∀ueⱽ.elementⱽ

    lda : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f} →
      Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]
      → Cᴰ [ f ][ Γᴰ , vert ]
    lda = ∀ueⱽ.universalⱽ .fst

    lda⟨_⟩⟨_⟩ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f g}
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
      {gᴰ : Cᴰ [ bp.×aF ⟪ g ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
      → f ≡ g
      → Path Cᴰ.Hom[ _ , _ ]
          (_ , fᴰ)
          (_ , gᴰ)
      → Path Cᴰ.Hom[ _ , _ ]
          (_ , lda fᴰ)
          (_ , lda gᴰ)
    lda⟨ f≡g ⟩⟨ fᴰ≡gᴰ ⟩ =
      ∀ueⱽ.∫ue.intro⟨ ΣPathP (f≡g , (Cᴰ.rectify $ Cᴰ.≡out fᴰ≡gᴰ)) ⟩

    ∀β : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f} →
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
      → Path Cᴰ.Hom[ _ , _ ]
          ((bp.×aF ⟪ f ⟫ C.⋆ bp.×aF ⟪ C.id ⟫) , (weakenⱽ .F-homᴰ (lda fᴰ) Cᴰ.⋆ᴰ app))
          (bp.×aF ⟪ f ⟫ , fᴰ)
    ∀β =
      Cᴰ.reind-filler _ _
      ∙ Cᴰ.reind-filler _ _
      ∙ (Cᴰ.≡in $ ∀ueⱽ.βⱽ)

    ∀η : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f}
      {fᴰ : Cᴰ [ f ][ Γᴰ , vert ]}
      → Path Cᴰ.Hom[ _ , _ ]
          (f , fᴰ)
          (f , lda (Cᴰ.reind (sym (bp.×aF .F-seq _ _) ∙ cong (bp.×aF .F-hom) (C.⋆IdR _))
            (weakenⱽ .F-homᴰ fᴰ Cᴰ.⋆ᴰ app)))
    ∀η = (Cᴰ.≡in $ ∀ueⱽ.ηⱽ)
      ∙ lda⟨ refl ⟩⟨ sym (Cᴰ.reind-filler _ _) ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.reind-filler _ _ ⟩

    lda≡ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}{f g}
      {fᴰ : Cᴰ [ bp.×aF ⟪ f ⟫ ][ f*yᴰ Γᴰ bp.π₁ , pᴰ ]}
      {gᴰ : Cᴰ [ g ][ Γᴰ , vert ]}
      → f ≡ g
      → Path Cᴰ.Hom[ _ , _ ]
          (bp.×aF ⟪ f ⟫ , fᴰ)
          ((bp.×aF ⟪ g ⟫ C.⋆ bp.×aF ⟪ C.id ⟫), (weakenⱽ .F-homᴰ gᴰ Cᴰ.⋆ᴰ app))
      → Path Cᴰ.Hom[ _ , _ ]
          (f , lda fᴰ)
          (g , gᴰ)
    lda≡ f≡g fᴰ≡gᴰπ =
      lda⟨ f≡g ⟩⟨ fᴰ≡gᴰπ ∙ Cᴰ.reind-filler _ _ ⟩
      ∙ sym ∀η

--   -- --   vert : Cᴰ.ob[ a ]
--   -- --   vert = ∀ueⱽ.vertexᴰ

--   -- --   app  : Cᴰ [ C.id ×p C.id ][ f*yᴰ vert π₁ , pᴰ ]
--   -- --   app = ∀ueⱽ.elementᴰ

--   -- --   lda : ∀ {Γ : Cᴰ.ob[ a ]} →
--   -- --     Cᴰ [ C.id ×p C.id ][ f*yᴰ Γ π₁ , pᴰ ] →
--   -- --     Cᴰ [ C.id ][ Γ , vert ]
--   -- --   lda fᴰ = ∀ueⱽ.introⱽ fᴰ

-- --   -- -- -- TODO: it may be useful to prove the following:
-- --   -- -- -- This definition includes the Beck condition that the quantifier
-- --   -- -- -- is preserved by cartesian lifts, i.e., that quantifiers commute
-- --   -- -- -- with substitution
-- --   -- -- -- Cᴰ [ f ][ Γᴰ , g* (∀ pᴰ) ]
-- --   -- -- -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
-- --   -- -- -- ≅ Cᴰ [ f ⋆ g ][ Γᴰ , ∀ pᴰ ]
-- --   -- -- -- ≅ Cᴰ [ (f ⋆ g) × b ][ π₁* Γᴰ , pᴰ ]
-- --   -- -- -- ≅ Cᴰ [ (f × b) ⋆ (g × b) ][ π₁* Γᴰ , pᴰ ]
-- --   -- -- -- ≅ Cᴰ [ (f × b) ][ π₁* Γᴰ , (g ⋆ b)* pᴰ ]
-- --   -- -- -- ≅ Cᴰ [ f ][ Γᴰ , ∀ (g ⋆ b)* pᴰ ]


module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (bp : BinProducts C)
  (isFib : isFibration Cᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ

  UniversalQuantifiers : Type _
  UniversalQuantifiers = ∀ a Γ pᴰ
    → UniversalQuantifier {a = a} (λ c → bp (c , a)) isFib {Γ = Γ} pᴰ
  -- module UniversalQuantifiersNotation (∀ᴰ : UniversalQuantifiers) where
  --   module _ {a b}{pᴰ : Cᴰ.ob[ a × b ]} where
  --     open UniversalQuantifierNotation (∀ᴰ pᴰ) hiding (module ∀ueⱽ) public
  --   module ∀ueⱽ {a b}(pᴰ : Cᴰ.ob[ a × b ]) =
  --     UniversalQuantifierNotation.∀ueⱽ (∀ᴰ pᴰ)
