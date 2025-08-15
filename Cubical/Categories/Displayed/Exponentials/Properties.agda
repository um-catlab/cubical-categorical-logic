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
          the-elt' : Cᴰ [ _ C.⋆ _ C.⋆ c⇒d.app ][ isFib.f*yᴰ (uq .vertexⱽ) bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
          the-elt' = ((bpⱽ.π₁ Cᴰ.⋆ᴰ uq.app) bpⱽ.,ⱽ (bpⱽ.π₂ Cᴰ.⋆ᴰ Cᴰ.reind (sym $ -×c.×aF .Functor.F-id) Cᴰ.idᴰ)) Cᴰ.⋆ᴰ expⱽ.app Cᴰ.⋆ᴰ isFib.π

          the-elt : Cᴰ [ c⇒d.app ][ isFib.f*yᴰ uq.vert bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
          the-elt = Cᴰ.reind (cong₂ C._⋆_ (C.⋆IdL _ ∙ -×c.×aF .Functor.F-id) (C.⋆IdL _) ∙ C.⋆IdL _) the-elt'

        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ :
          Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .vertexᴰ = uq.vert
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ  .elementᴰ = the-elt
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ {x = x}{xᴰ = xᴰ} .isIsoOver.inv f fᴰ =
          -- Given f : x × c → d
          --       fᴰ : π₁* xᴰ ×ⱽ π₂* cᴰ → dᴰ over f
          -- Want a map xᴰ → ∀ (π₂* cᴰ ⇒ app* dᴰ) over λf
          -- Via ∀λ, it suffices to build a map π₁* xᴰ → (π₂* cᴰ ⇒ app* dᴰ) over (λf × id)
          -- To build this map, we use λ for the exponential structure on (λf × id)* (π₂* cᴰ ⇒ app* dᴰ)
          --   as it an exponential in the fiber over (x × c)
          -- Thus it reduces to building a map π₁* xᴰ ×ⱽ (λf × id)* π₂* cᴰ → (λ f × id)* (app* dᴰ)

          uq.lda $ expⱽ.lda $ isFib.introCL $ Cᴰ.reind p $
               -- This is just the intro of the induced displayed binary product for (bpⱽ.π₁ Cᴰ.⋆ᴰ isFib.π) and (bpⱽ.π₂ Cᴰ.⋆ᴰ isFib.π Cᴰ.⋆ᴰ isFib.π)
               -- but I want to lay everything out in terms of vertical products to understand this proof
               (isFib.introCL (Cᴰ.reind (sym bp.×β₁) $ (bpⱽ.π₁ Cᴰ.⋆ᴰ isFib.π)) bpⱽ.,ⱽ isFib.introCL (Cᴰ.reind (sym bp.×β₂) $ (bpⱽ.π₂ Cᴰ.⋆ᴰ isFib.π Cᴰ.⋆ᴰ isFib.π)))
               Cᴰ.⋆ᴰ fᴰ
          where
          λf×id = -×c.×aF ⟪ c⇒d.lda f ⟫

          p : (((C.id C.⋆ bp.π₁) bp.,p (C.id C.⋆ λf×id C.⋆ bp.π₂)) C.⋆ f) ≡ λf×id C.⋆ c⇒d.app
          p =
            cong (C._⋆ f) (cong₂ bp._,p_ (C.⋆IdL _) (C.⋆IdL _))
            ∙ cong₂ C._⋆_ (bp.,p≡ (sym $ C.⋆IdL _) (bp.×β₂ ∙ (sym $ C.⋆IdL _))) refl
            ∙ C.⋆IdL _
            ∙ sym c⇒d.⇒ue.β
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.rightInv f fᴰ =
          Cᴰ.rectify $ Cᴰ.≡out $
            -- Goal:
            -- _ , ((isFib.introCL (Cᴰ.reind (sym bp.×β₁) $
            --       (bpᴰ.π₁ᴰ Cᴰ.⋆ᴰ
            --         (uq.lda $ expⱽ.lda $ isFib.introCL $ Cᴰ.reind p $
            --           (isFib.introCL (Cᴰ.reind (sym bp.×β₁) $ (bpⱽ.π₁ Cᴰ.⋆ᴰ isFib.π)) bpⱽ.,ⱽ isFib.introCL (Cᴰ.reind (sym bp.×β₂) $ (bpⱽ.π₂ Cᴰ.⋆ᴰ isFib.π Cᴰ.⋆ᴰ isFib.π))) Cᴰ.⋆ᴰ fᴰ)))
            --      bpⱽ.,ⱽ
            --      isFib.introCL (Cᴰ.reind (sym bp.×β₂) $ bpᴰ.π₂ᴰ))
            --      Cᴰ.⋆ᴰ the-elt)
            --   ≡⟨ {!!} ⟩
            -- f , fᴰ
            -- ∎
            {!!}
            -- TODO
            -- sym reind-filler on the-elt to expose the binary product
            -- then compose binary products and reduce
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
