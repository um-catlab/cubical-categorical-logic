{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Exponentials where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Functor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Presheaf

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
  hiding (π; reindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Category
open Functor
open UniversalElement
open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where

  open isIsoOver
  private
    module C = Category C
    module D = Category D
    F*Dᴰ = Base.reindex Dᴰ F
    module F*Dᴰ = Fibers F*Dᴰ
    module Dᴰ = Fibers Dᴰ

  module _ {c : C .ob} {Fcᴰ Fcᴰ' : Dᴰ.ob[ F ⟅ c ⟆ ]}
    (isFib : isFibration Dᴰ)
    (bpⱽ : BinProductsⱽ Dᴰ)
    (exp : Exponentialⱽ Dᴰ bpⱽ isFib Fcᴰ Fcᴰ')
    where

    private
      module Fcᴰ⇒Fcᴰ' = Exponentialⱽ exp
      module id*⟨Fcᴰ⇒Fcᴰ'⟩ = Fcᴰ⇒Fcᴰ'.f*⟨cᴰ⇒cᴰ'⟩ D.id
      module isFib = isFibrationNotation Dᴰ isFib

    open Exponentialⱽ
    module bpⱽ = BinProductsⱽNotation Dᴰ bpⱽ

    preservesExponentialⱽ :
      Exponentialⱽ (Base.reindex Dᴰ F) (BinProductsⱽReindex bpⱽ) (isFibrationReindex _ F isFib)
        Fcᴰ Fcᴰ'
    preservesExponentialⱽ .vertex = Fcᴰ⇒Fcᴰ'.vertex
    preservesExponentialⱽ .element = Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.element
    preservesExponentialⱽ .becomes-universal f Fbᴰ =
      isIsoToIsEquiv (
        (λ fⱽ → Dᴰ.reind (sym $ F .F-id) $ f*⟨Fcᴰ⇒Fcᴰ'⟩.lda (Dᴰ.reind (F .F-id) $ fⱽ)) ,
        (λ fⱽ →
            Dᴰ.rectify $ Dᴰ.≡out $
              (sym $ Dᴰ.reind-filler _ _)
              ∙ (sym $ Dᴰ.reind-filler _ _)
              ∙ {!!}
              -- ∙ Dᴰ.⟨ bpⱽ.⟨(sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙
              --             Dᴰ.⟨ (sym $ Dᴰ.reind-filler _ _) ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _)∙ refl ⟩ ∙ Dᴰ.reind-filler _ _
              --      ⟩,ⱽ⟨ (sym $ Dᴰ.reind-filler _ _) ⟩
              --      ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _)
              --        ∙ Dᴰ.⟨ (Dᴰ.reind-filler (F .F-id) _) ∙ {!!}
              --           ⟩⋆⟨ isFib.introCL⟨_⟩⟨_⟩ Fcᴰ' (F-hom F f) (F .F-id) ((sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙
              --               Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ∙ Dᴰ.reind-filler _ _ ⟩) ⟩ ∙ Dᴰ.reind-filler _ _ ⟩
              -- ∙ (Dᴰ.reind-filler _ _)
              ∙ (Dᴰ.≡in $ f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.β)
              ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
        ) ,
        {!!}
      )
      where module f*⟨Fcᴰ⇒Fcᴰ'⟩ = Fcᴰ⇒Fcᴰ'.f*⟨cᴰ⇒cᴰ'⟩ (F ⟪ f ⟫)
    -- preservesExponentialⱽ .becomes-universal f Fbᴰ .equiv-proof gᴰ .fst .fst = Dᴰ.reind (sym $ F .F-id) $ f*⟨Fcᴰ⇒Fcᴰ'⟩.lda (Dᴰ.reind (F .F-id) $ gᴰ)
    --   where module f*⟨Fcᴰ⇒Fcᴰ'⟩ = Fcᴰ⇒Fcᴰ'.f*⟨cᴰ⇒cᴰ'⟩ (F ⟪ f ⟫)
    -- preservesExponentialⱽ .becomes-universal f Fbᴰ .equiv-proof gᴰ .fst .snd =
    --   Dᴰ.rectify $ Dᴰ.≡out $
    --     (sym $ Dᴰ.reind-filler _ _)
    --     ∙ (sym $ Dᴰ.reind-filler _ _)
    --     ∙ Dᴰ.⟨ {!!} ⟩⋆⟨ {!!} ⟩
    --     ∙ {!!}
    --     ∙ {!!}
    --     ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
    --   -- {!f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.β!}
    --   where module f*⟨Fcᴰ⇒Fcᴰ'⟩ = Fcᴰ⇒Fcᴰ'.f*⟨cᴰ⇒cᴰ'⟩ (F ⟪ f ⟫)
    -- preservesExponentialⱽ .becomes-universal f Fbᴰ .equiv-proof gᴰ .snd = {!!}
      -- isIsoToIsEquiv (
        -- (λ fⱽ → Dᴰ.reind (sym $ F .F-id) $ f*⟨Fcᴰ⇒Fcᴰ'⟩.lda (F .F-hom f) (Dᴰ.reind (F .F-id) fⱽ)) ,
        -- (λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
        --     (sym $ Dᴰ.reind-filler _ _)
        --     ∙ (sym $ Dᴰ.reind-filler _ _)
        --     ∙ {!f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.intro≡ (F .F-hom f) ?!}
        --     ∙ {!!}
        --     -- ∙ Dᴰ.⟨ bpⱽ.⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _)
        --     --      ⟩,ⱽ⟨ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.reind-filler ((sym $ F .F-id)
        --     --         ∙ (sym $ D.⋆IdR _) ∙ λ i → F .F-hom C.id D.⋆ F .F-id (~ i)) _ ⟩ ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _)⟩
        --     -- -- ∙ Dᴰ.⟨ bpⱽ.⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ {!!} ⟩,ⱽ⟨ {!!} ⟩ ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _)∙ {!!} ⟩
        --     -- ∙ Dᴰ.⟨ bpⱽ.⟨ {!!} ⟩,ⱽ⟨ {!!} ⟩ ⟩⋆⟨ {!!} ⟩
        --     -- ∙ Dᴰ.reind-filler _ _
        --     -- ∙ (Dᴰ.≡in $ f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.β (F-hom F f))
        --     -- ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
        -- ) ,
        -- λ fⱽ →
        --   Dᴰ.rectify $ Dᴰ.≡out $
        --     (sym $ Dᴰ.reind-filler _ _)
        --     ∙ {!f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.intro≡ (F .F-hom f) ?!}
        --     ∙ {!f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.intro≡ (F .F-hom f) ?!}
        --     ∙ {!!}
        -- )
    -- {!Fcᴰ⇒Fcᴰ'.becomes-universal (F .F-hom f) Fbᴰ!}
      -- isIsoToIsEquiv (
      --   (λ fⱽ → Dᴰ.reind (sym $ F .F-id) $ f*⟨Fcᴰ⇒Fcᴰ'⟩.lda (F .F-hom f) (Dᴰ.reind (F .F-id) fⱽ)) ,
      --   (λ fⱽ →
      --     Dᴰ.rectify $ Dᴰ.≡out $
      --       (sym $ Dᴰ.reind-filler _ _)
      --       ∙ (sym $ Dᴰ.reind-filler _ _)
      --       ∙ Dᴰ.⟨ bpⱽ.⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ {!refl!} ⟩,ⱽ⟨ {!refl!} ⟩
      --            ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ {!!} ⟩
      --       ∙ Dᴰ.reind-filler _ _
      --       ∙ (Dᴰ.≡in $ f*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.β (F-hom F f))
      --       ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
      --   ) ,
      --   {!!}
      -- )

    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .vertex = Fcᴰ⇒Fcᴰ'.vert
    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .element =
    --   Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.app
    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .universal dᴰ = isIsoToIsEquiv
    --   ( (λ fⱽ → Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.lda (Dᴰ.reind (F .F-id) fⱽ))
    --   , (λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
    --     (sym $ Dᴰ.reind-filler _ _)
    --     ∙ (sym $ Dᴰ.reind-filler _ _)
    --     ∙ Dᴰ.⟨ ⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ (sym $ Dᴰ.reind-filler _ _) ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ refl ⟩ ∙ Dᴰ.reind-filler _ _  ⟩,ⱽ⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
    --     ∙ Dᴰ.reind-filler _ _
    --     ∙ (Dᴰ.≡in $ Fcᴰ⇒Fcᴰ'.⇒ue.β)
    --     ∙ (sym $ Dᴰ.reind-filler (F .F-id) _))
    --   , λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
    --     (sym $ Dᴰ.reind-filler _ _)
    --     ∙ Fcᴰ⇒Fcᴰ'.intro≡ (
    --       (sym $ Dᴰ.reind-filler _ _)
    --       ∙ (sym $ Dᴰ.reind-filler _ _)
    --       ∙ (sym $ Dᴰ.reind-filler _ _)
    --       ∙ Dᴰ.⟨ ⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩ ∙ Dᴰ.reind-filler _ _ ⟩,ⱽ⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
    --       )
    --     ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
    --     )
    -- preservesExponentialⱽ .reindex⇒ {Γ} γ Γᴰ = isIsoToIsEquiv
    --   ( (λ fⱽ →
    --     Dᴰ.reind (sym $ F .F-id) $ Fγ*⟨Fcᴰ⇒Fcᴰ'⟩.lda (Dᴰ.reind (F .F-id) fⱽ)
    --     )
    --   , (λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
    --     {!!}
    --     ∙ (Dᴰ.≡in $ Fγ*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.β)
    --     ∙ (sym $ Dᴰ.reind-filler (F .F-id) _))
    --   , λ gⱽ → Dᴰ.rectify $ Dᴰ.≡out $
    --     (sym $ Dᴰ.reind-filler _ _)
    --     ∙ {!!}
    --   )
    --     -- ∙ (Dᴰ.≡in $ Fγ*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.intro⟨ Dᴰ.≡out $ Dᴰ.reind-filler _ _ ⟩)
    --     -- ∙ (Dᴰ.≡in $ {!Fγ*⟨Fcᴰ⇒Fcᴰ'⟩.⇒ue.η!}))
    --   where
    --     module Fγ*⟨Fcᴰ⇒Fcᴰ'⟩ = Fcᴰ⇒Fcᴰ'.f*⟨cᴰ⇒cᴰ'⟩ (F ⟪ γ ⟫)
