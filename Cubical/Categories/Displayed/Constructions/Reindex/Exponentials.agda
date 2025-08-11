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
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
  hiding (π; reindex)
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise

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
    (vbp : BinProductsⱽ Dᴰ)
    (exp : Exponentialⱽ Dᴰ vbp isFib Fcᴰ Fcᴰ')
    where

    open Exponentialⱽ
    module Fcᴰ⇒Fcᴰ' = Exponentialⱽ exp

    open BinProductsⱽNotation Dᴰ vbp

    preservesExponentialⱽ :
      Exponentialⱽ (Base.reindex Dᴰ F) (BinProductsⱽReindex vbp) (isFibrationReindex _ F isFib)
        Fcᴰ Fcᴰ'
    preservesExponentialⱽ .cᴰ⇒cᴰ' .vertex = Fcᴰ⇒Fcᴰ'.vert
    preservesExponentialⱽ .cᴰ⇒cᴰ' .element =
      Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.app
    preservesExponentialⱽ .cᴰ⇒cᴰ' .universal dᴰ = isIsoToIsEquiv
      ( (λ fⱽ → Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.lda (Dᴰ.reind (F .F-id) fⱽ))
      , (λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
        (sym $ Dᴰ.reind-filler _ _)
        ∙ (sym $ Dᴰ.reind-filler _ _)
        ∙ Dᴰ.⟨ ⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ (sym $ Dᴰ.reind-filler _ _) ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ refl ⟩ ∙ Dᴰ.reind-filler _ _  ⟩,ⱽ⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
        ∙ Dᴰ.reind-filler _ _
        ∙ (Dᴰ.≡in $ Fcᴰ⇒Fcᴰ'.⇒ue.β)
        ∙ (sym $ Dᴰ.reind-filler (F .F-id) _))
      , λ fⱽ → Dᴰ.rectify $ Dᴰ.≡out $
        (sym $ Dᴰ.reind-filler _ _)
        ∙ Fcᴰ⇒Fcᴰ'.intro≡ (
          (sym $ Dᴰ.reind-filler _ _)
          ∙ {! ⟨ ? ⟩,ⱽ⟨ ? ⟩ !}
          )
        ∙ (sym $ Dᴰ.reind-filler (F .F-id) _)
        )
    -- .equiv-proof fᴰ .fst .fst =
    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .universal dᴰ .equiv-proof fᴰ .fst .fst =
    --   Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.lda (Dᴰ.reind (F .F-id) fᴰ)
    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .universal dᴰ .equiv-proof fᴰ .fst .snd = {!!}
    --   -- (P ⟪(Dᴰ.reind (sym $ F .F-id) $
    --   --     exp .cᴰ⇒cᴰ' .universal dᴰ .equiv-proof (Dᴰ.reind (F .F-id) fᴰ) .fst .fst)⟫ $
    --   --     Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.app)
    --   --   ≡⟨ refl ⟩
    --   -- ({!!} $ Dᴰ.reind (sym $ F .F-id) $ Fcᴰ⇒Fcᴰ'.app)
    --   --   ≡⟨ {!!} ⟩
    --   -- fᴰ
    --   -- ∎
    --   where
    --   P : Presheaf F*Dᴰ.v[ c ] ℓDᴰ'
    --   P = ExponentiableProf F*Dᴰ.v[ c ] _ .F-ob Fcᴰ'

    --   -- Dᴰ.rectify $ Dᴰ.≡out $
    --   --   (sym $ Dᴰ.reind-filler _ _)
    --   --   ∙ (sym $ Dᴰ.reind-filler _ _)
    --   --   ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
    --   --   ∙ {!!}
    --   --   ∙ Dᴰ.reind-filler _ _
    --   --   ∙ (λ i → (D.id , exp .cᴰ⇒cᴰ' .universal dᴰ .equiv-proof (Dᴰ.reind (F .F-id) fᴰ) .fst .snd i))
    --   --   ∙ (sym $ Dᴰ.reind-filler (F .F-id) fᴰ)
    -- preservesExponentialⱽ .cᴰ⇒cᴰ' .universal dᴰ .equiv-proof fᴰ .snd = {!!}
    --   -- isIsoToIsEquiv (
    --   --   (λ y → Dᴰ.reind (sym $ F .F-id) $ exp .cᴰ⇒cᴰ' .universal x .equiv-proof (Dᴰ.reind (F .F-id) y) .fst .fst) ,
    --   --   (λ y →
    --   --     Dᴰ.rectify $ Dᴰ.≡out $
    --   --       (sym $ Dᴰ.reind-filler _ _)
    --   --       ∙ (sym $ Dᴰ.reind-filler _ _)
    --   --       ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
    --   --       ∙ Dᴰ.reind-filler (D.⋆IdR (F .F-hom C.id)) _
    --   --       ∙ ΣPathP (refl , {!exp .cᴰ⇒cᴰ' .universal x .equiv-proof (Dᴰ.reind (F .F-id) y) .fst .snd!})
    --   --     ) ,
    --   --   {!!})
    preservesExponentialⱽ .reindex⇒ = {!!}
