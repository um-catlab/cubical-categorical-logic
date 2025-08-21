{-# OPTIONS --safe --lossy-unification #-}
{-
  Displayed and Vertical Exponentials

  Displayed Exponentials are fairly straightforward but Vertical Exponentials
  are less nice. Here we have defined them in the textbook way: exponential in
  each fiber that's preserved by reindexing.
-}
module Cubical.Categories.Displayed.Exponentials.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Fibration.Properties
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Quantifiers
open import Cubical.Categories.Displayed.Exponentials.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level


module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (bp : BinProducts C)
    (bpⱽ : BinProductsⱽ Cᴰ)
    (isFib : isFibration Cᴰ)
  where

  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
    module isFib = isFibrationNotation _ isFib
    module bp = BinProductsNotation bp

    bpᴰ : BinProductsᴰ Cᴰ bp
    bpᴰ = BinProductsⱽ→BinProductsᴰ Cᴰ isFib bpⱽ bp
    module bpᴰ = BinProductsᴰNotation bpᴰ
    module bpⱽ = BinProductsⱽNotation _ bpⱽ

  module _
    {c d : C.ob}
    {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Cᴰ.ob[ d ]}
    (exp : Exponential C c d (λ c' → bp (c' , c)))
    where

    private
      module c⇒d = ExponentialNotation _ exp
      module -×c = BinProductsWithNotation (λ c' → bp (c' , c))

    module _
      (expⱽ : Exponentialⱽ Cᴰ bpⱽ isFib (isFib.f*yᴰ cᴰ bp.π₂) (isFib.f*yᴰ dᴰ c⇒d.app))
      where

      module expⱽ = Exponentialⱽ expⱽ

      open UniversalElementᴰ
      open UniversalElementⱽ

      module _
        (uq : UniversalQuantifier (λ c' → bp (c' , c)) isFib (expⱽ.vertex))
        where

        module uq = UniversalQuantifierNotation _ isFib uq

        private
          the-elt : Cᴰ [ c⇒d.app ][ isFib.f*yᴰ uq.vert bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
          the-elt = (Cᴰ.reind (-×c.×aF .Functor.F-id) uq.app bpⱽ.×p Cᴰ.idᴰ) Cᴰ.⋆ⱽᴰ (expⱽ.app Cᴰ.⋆ⱽᴰ isFib.π)

        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ :
          Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .vertexᴰ = uq.vert
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ  .elementᴰ = the-elt
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ {x = x}{xᴰ = xᴰ} .isIsoOver.inv f fᴰ =
          uq.lda $ expⱽ.lda {f = λf×id} $ Cᴰ.reind (C.⋆IdL _) $ ((Cᴰ.idᴰ bpⱽ.×p isFib.introCLⱽ (Cᴰ.reind bp.×β₂ (isFib.π Cᴰ.⋆ᴰ isFib.π))) Cᴰ.⋆ᴰ isFib.introCL (Cᴰ.reind (sym c⇒d.⇒ue.β) fᴰ))
          where
          λf×id = -×c.×aF ⟪ c⇒d.lda f ⟫

          p : C.id C.⋆ f ≡ (λf×id C.⋆ c⇒d.app)
          p =  C.⋆IdL _ ∙ sym c⇒d.⇒ue.β

        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.rightInv f fᴰ =
          Cᴰ.rectify $ Cᴰ.≡out $
           {!!}
           -- These equalities are commented out for perfromance. They fill the gap between the left endpoint and the WIP equality term below
           --  Cᴰ.⟨
           --    bpⱽ.⟨ isFib.introCL⟨ refl ⟩⟨
           --      (sym $ Cᴰ.reind-filler _ _)
           --      ∙ Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ refl ⟩ ⟩⋆⟨ refl ⟩
           --      ∙ Cᴰ.⋆Assoc _ _ _
           --      ∙ Cᴰ.reind-filler (C.⋆IdL _ ∙ sym bp.×β₁) _
           --     ⟩
           --   ⟩,ⱽ⟨
           --     isFib.introCL⟨ refl ⟩⟨
           --       (sym $ Cᴰ.reind-filler _ _)
           --     ∙ (sym $ Cᴰ.reind-filler _ _)
           --     ∙ Cᴰ.reind-filler (C.⋆IdL _ ∙ sym bp.×β₂) _
           --     ⟩
           --   ⟩
           -- ⟩⋆⟨
           --   (sym $ Cᴰ.reind-filler _ _)
           --   ∙ Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ⟩⋆⟨ refl ⟩
           -- ⟩
           -- ∙ Cᴰ.⟨
           --     bpⱽ.⟨
           --       isFib.introCL⟨ refl ∙ (sym $ C.⋆IdL _) ⟩⟨
           --         (sym $ Cᴰ.reind-filler _ _)
           --         ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler (sym bp.×β₁) _ ⟩
           --         ∙ Cᴰ.reind-filler _ _
           --       ⟩
           --       ∙ (sym $ isFib.introCL-natural)
           --     ⟩,ⱽ⟨
           --       Cᴰ.reind-filler (sym $ C.⋆IdL _) _
           --     ⟩
           --   ⟩⋆⟨
           --     refl
           --   ⟩
           --  ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
           --  ∙ Cᴰ.⟨ bpⱽ.,ⱽ-seq ∙ bpⱽ.⟨ (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ uq.∀β ⟩ ⟩,ⱽ⟨ Cᴰ.reind-filler _ _ ⟩ ⟩⋆⟨ refl ⟩
            ∙ (
              _ , (((bpⱽ.π₁ Cᴰ.⋆ᴰ expⱽ.lda _) bpⱽ.,ⱽ Cᴰ.reind _ (Cᴰ.reind _ (isFib.introCL _) Cᴰ.⋆ᴰ Cᴰ.idᴰ)) Cᴰ.⋆ᴰ Cᴰ.reind _ (expⱽ.app Cᴰ.⋆ᴰ isFib.π))
                ≡⟨
                 Cᴰ.⟨
                   bpⱽ.⟨
                     refl
                   ⟩,ⱽ⟨
                     (sym $ Cᴰ.reind-filler _ _)
                     ∙ Cᴰ.⟨
                         (sym $ Cᴰ.reind-filler _ _)
                       ⟩⋆⟨
                         refl
                       ⟩
                       ∙ Cᴰ.⋆IdR _
                     ⟩
                   ⟩⋆⟨
                     (sym $ Cᴰ.reind-filler _ _)
                   ⟩
                   ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
                   -- TODO need to rewrite
                   --    ((bpⱽ.π₁ Cᴰ.⋆ᴰ expⱽ.lda _) bpⱽ.,ⱽ isFib.introCL _)
                   --    as
                   --    ? Cᴰ.⋆ᴰ (expⱽ.lda bpⱽ.×p isFib.π)
                   ∙ Cᴰ.⟨ Cᴰ.⟨ {!!} ⟩⋆⟨ refl ⟩ ∙ (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ expⱽ.β⇒ⱽ {fᴰ = Cᴰ.reind (C.⋆IdL _) $ ((Cᴰ.idᴰ bpⱽ.×p isFib.introCLⱽ (Cᴰ.reind bp.×β₂ (isFib.π Cᴰ.⋆ᴰ isFib.π))) Cᴰ.⋆ᴰ isFib.introCL (Cᴰ.reind (sym c⇒d.⇒ue.β) fᴰ))} ⟩ ⟩⋆⟨ refl ⟩
                   ∙ Cᴰ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ (sym $ Cᴰ.⋆Assoc _ _ _) ∙ isFib.introCL-natural ∙ isFib.introCL⟨ {!!} ⟩⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ {!!} ⟩⋆⟨ refl ⟩ ∙ Cᴰ.⋆IdL _ ⟩ ⟩⋆⟨ refl ⟩
                   ∙ isFib.βCL
                   ∙ (sym $ Cᴰ.reind-filler _ _)
                 ⟩
              f , fᴰ
              ∎)
          where
          λf×id = -×c.×aF ⟪ c⇒d.lda f ⟫

          -×cᴰ = BinProductWithFᴰ Cᴰ (λ c' → bp (c' , c)) λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)

          p : (((C.id C.⋆ bp.π₁) bp.,p (C.id C.⋆ λf×id C.⋆ bp.π₂)) C.⋆ f) ≡ λf×id C.⋆ c⇒d.app
          p =
            cong (C._⋆ f) (cong₂ bp._,p_ (C.⋆IdL _) (C.⋆IdL _))
            ∙ cong₂ C._⋆_ (bp.,p≡ (sym $ C.⋆IdL _) (bp.×β₂ ∙ (sym $ C.⋆IdL _))) refl
            ∙ C.⋆IdL _
            ∙ sym c⇒d.⇒ue.β
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.leftInv = {!!}
