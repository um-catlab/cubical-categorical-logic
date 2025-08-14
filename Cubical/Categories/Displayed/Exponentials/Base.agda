{-# OPTIONS --safe --lossy-unification #-}
{-
  Displayed and Vertical Exponentials

  Displayed Exponentials are fairly straightforward but Vertical Exponentials
  are less nice. Here we have defined them in the textbook way: exponential in
  each fiber that's preserved by reindexing.
-}
module Cubical.Categories.Displayed.Exponentials.Base where

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

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
  Exponentialᴰ :
    ∀ {c d} { -×c : BinProductsWith C c}
    cᴰ (dᴰ : Cᴰ.ob[ d ]) (-×ᴰcᴰ : BinProductsWithᴰ Cᴰ -×c cᴰ)
    → (c⇒d : Exponential C c d -×c)
    → Type _
  Exponentialᴰ cᴰ dᴰ -×ᴰcᴰ c⇒d = RightAdjointAtᴰ (BinProductWithFᴰ Cᴰ _ -×ᴰcᴰ) c⇒d dᴰ

  Exponentialsᴰ : ∀ bp
    → Exponentials C bp
    → BinProductsᴰ Cᴰ bp
    → Type _
  Exponentialsᴰ bp exps bpᴰ = ∀ {c d} (cᴰ : Cᴰ.ob[ c ])(dᴰ : Cᴰ.ob[ d ])
    → Exponentialᴰ cᴰ dᴰ (λ _ xᴰ → bpᴰ (xᴰ , cᴰ)) (AnExponential C bp exps)

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ (bpⱽ : BinProductsⱽ Cᴰ) (isFib : isFibration Cᴰ)
    where

    private
      module bpⱽ = BinProductsⱽNotation _ bpⱽ
      module isFib = isFibrationNotation Cᴰ isFib

    open bpⱽ
    open Functorᴰ

    record Exponentialⱽ {c : C.ob} (cᴰ cᴰ' : Cᴰ.ob[ c ]) : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ') where
      no-eta-equality
      field
        vertex : Cᴰ.ob[ c ]
        element : Cᴰ.v[ c ] [ vertex ×ⱽ cᴰ , cᴰ' ]
        becomes-universal : ∀ {b} (f : C [ b , c ]) →
          becomesExponential (isFib.f*F f)
            (BinProductsWithⱽ→BinProductsWithFiber Cᴰ λ cᴰ'' → bpⱽ _ _)
            (λ _ → cartesianLift-preserves-BinProductFiber Cᴰ isFib (bpⱽ _ _) f)
            (BinProductsWithⱽ→BinProductsWithFiber Cᴰ λ cᴰ'' → bpⱽ _ _)
            vertex
            element

      module _ {b} {f : C [ b , c ]} where
        -- TODO: move BinProductsWithⱽ→BinProductsWithFiber into some kind of notation
        f*⟨cᴰ⇒cᴰ'⟩ : Exponential Cᴰ.v[ b ] (isFib.f*yᴰ cᴰ f) (isFib.f*yᴰ cᴰ' f)
                       (BinProductsWithⱽ→BinProductsWithFiber Cᴰ (λ cᴰ'' → bpⱽ _ _))
        f*⟨cᴰ⇒cᴰ'⟩ = becomesExponential→Exponential _ _ _ _ (becomes-universal f)

        module f*⟨cᴰ⇒cᴰ'⟩ = ExponentialNotation _ f*⟨cᴰ⇒cᴰ'⟩

      lda :
        ∀ {Γ}{f : C [ Γ , c ]}{Γᴰ}
        → Cᴰ.Hom[ f ][ Γᴰ ×ⱽ isFib.f*yᴰ cᴰ f , cᴰ' ]
        → Cᴰ.Hom[ f ][ Γᴰ , vertex ]
      lda fᴰ⟨x⟩ = f*⟨cᴰ⇒cᴰ'⟩.lda (isFib.introCLⱽ fᴰ⟨x⟩) Cᴰ.⋆ⱽᴰ isFib.π

      app : Cᴰ.v[ _ ] [ vertex ×ⱽ cᴰ , cᴰ' ]
      app =
        (isFib.introCLⱽ bpⱽ.π₁ ,ⱽ isFib.introCLⱽ bpⱽ.π₂)
        Cᴰ.⋆ⱽ f*⟨cᴰ⇒cᴰ'⟩.app
        Cᴰ.⋆ⱽ isFib.π

      -- β⇒ⱽ :
      --   ∀ {Γ}{f : C [ Γ , c ]}{Γᴰ}
      --   → {fᴰ : Cᴰ.Hom[ f ][ Γᴰ ×ⱽ isFib.f*yᴰ cᴰ f , cᴰ' ]}
      --   → Path Cᴰ.Hom[ _ , _ ]
      --       (_ , (BinProductFⱽ .F-homᴰ ((lda fᴰ) , isFib.π) Cᴰ.⋆ᴰ app))
      --       (_ , fᴰ)
      -- β⇒ⱽ =
      --   Cᴰ.⟨ {!!} ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ∙ {!!} ⟩
      --   ∙ {!!}
      --   ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
      --   ∙ Cᴰ.⟨ (refl ∙ Cᴰ.reind-filler _ _) ∙ (Cᴰ.≡in $ f*⟨cᴰ⇒cᴰ'⟩.⇒ue.β) ⟩⋆⟨ refl ⟩
      --   ∙ isFib.βⱽCL

      -- TODO: rename the following
      lda≡ :
        ∀ {x : C.ob}{f : C [ x , c ]}{g} →
        {xᴰ : Cᴰ.ob[ x ]} →
        {fᴰ : Cᴰ.Hom[ C.id ][ xᴰ ×ⱽ isFib.f*yᴰ cᴰ f , isFib.f*yᴰ cᴰ' f ]}
        {gᴰ : Cᴰ.Hom[ g ][ xᴰ , f*⟨cᴰ⇒cᴰ'⟩.vert ]}
        → (p : g ≡ C.id)
        → Path Cᴰ.Hom[ _ , _ ]
            (C.id , fᴰ)
            ((C.id C.⋆ C.id) , (((π₁ Cᴰ.⋆ⱽ Cᴰ.reind p gᴰ) ,ⱽ π₂) Cᴰ.⋆ᴰ f*⟨cᴰ⇒cᴰ'⟩.app))
        → Path Cᴰ.Hom[ _ , _ ]
            (C.id , f*⟨cᴰ⇒cᴰ'⟩.lda fᴰ)
            (g , gᴰ)
      lda≡ {f = f} g≡id p =
        Cᴰ.≡in (f*⟨cᴰ⇒cᴰ'⟩.⇒ue.intro≡ (Cᴰ.rectify $ Cᴰ.≡out $ p ∙ Cᴰ.reind-filler _ _)) ∙ (sym $ Cᴰ.reind-filler g≡id _)

    Exponentialsⱽ : Type _
    Exponentialsⱽ = ∀ {c} cᴰ cᴰ' → Exponentialⱽ {c} cᴰ cᴰ'

-- module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') (bp : BinProducts C)
--     (bpⱽ : BinProductsⱽ Cᴰ)
--     (isFib : isFibration Cᴰ)
--   where

--   private
--     module C = Category C
--     module Cᴰ = Fibers Cᴰ
--     module isFib = isFibrationNotation _ isFib
--     module bp = BinProductsNotation bp

--     bpᴰ : BinProductsᴰ Cᴰ bp
--     bpᴰ = BinProductsⱽ→BinProductsᴰ Cᴰ isFib bpⱽ bp
--     module bpᴰ = BinProductsᴰNotation bpᴰ
--     module bpⱽ = BinProductsⱽNotation _ bpⱽ

--   module _
--     {c d : C.ob}
--     {cᴰ : Cᴰ.ob[ c ]} {dᴰ : Cᴰ.ob[ d ]}
--     (exp : Exponential C c d (λ c' → bp (c' , c)))
--     where

--     private
--       module c⇒d = ExponentialNotation _ exp
--       module -×c = BinProductsWithNotation (λ c' → bp (c' , c))

--     module _
--       (expⱽ : Exponentialⱽ Cᴰ bpⱽ isFib (isFib.f*yᴰ cᴰ bp.π₂) (isFib.f*yᴰ dᴰ c⇒d.app))
--       where

--       open Exponentialⱽ
--       open UniversalElementᴰ
--       open UniversalElementⱽ

--       module _
--         (uq : UniversalQuantifier (λ c' → bp (c' , c)) isFib (expⱽ .vertex))
--         where

--         module uq = UniversalQuantifierNotation _ isFib uq

--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ :
--           Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .vertexᴰ = uq.vert
--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ  .elementᴰ = the-elt
--           where
--           fᴰ : Cᴰ [ C.id ][ isFib.f*yᴰ (uq .vertexⱽ) bp.π₁ , expⱽ .vertex ]
--           fᴰ = Cᴰ.reind (-×c.×aF .Functor.F-id) $ uq.app

--           gᴰ : Cᴰ [ _ C.⋆ _ C.⋆ c⇒d.app ][ isFib.f*yᴰ (uq .vertexⱽ) bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
--           gᴰ = ((bpⱽ.π₁ Cᴰ.⋆ᴰ fᴰ) bpⱽ.,ⱽ (bpⱽ.π₂ Cᴰ.⋆ᴰ Cᴰ.idᴰ)) Cᴰ.⋆ᴰ expⱽ .element Cᴰ.⋆ᴰ isFib.π

--           the-elt : Cᴰ [ c⇒d.app ][ isFib.f*yᴰ uq.vert bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
--           the-elt =
--             Cᴰ.reind
--               ((λ i → C.⋆IdL C.id i C.⋆ C.id C.⋆ c⇒d.app)
--               ∙ C.⋆IdL _
--               ∙ C.⋆IdL _)
--               gᴰ
--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ {x = x}{xᴰ = xᴰ} .isIsoOver.inv f fᴰ =
--           -- Given f : x × c → d
--           --       fᴰ : π₁* xᴰ ×ⱽ π₂* cᴰ → dᴰ over f
--           -- Want a map xᴰ → ∀ (π₂* cᴰ ⇒ app* dᴰ) over λf
--           -- Via ∀λ, it suffices to build a map π₁* xᴰ → (π₂* cᴰ ⇒ app* dᴰ) over (λf × id)
--           -- To build this map, we use λ for the exponential structure on (λf × id)* (π₂* cᴰ ⇒ app* dᴰ)
--           --   as it an exponential in the fiber over (x × c)
--           -- Thus it reduces to building a map π₁* xᴰ ×ⱽ (λf × id)* π₂* cᴰ → (λ f × id)* (app* dᴰ)
--           uq.lda gᴰ
--           where
--           λf×id = -×c.×aF ⟪ c⇒d.lda f ⟫
--           module ⟨λf×id⟩*⟨cᴰ⇒dᴰ⟩ = f*⟨cᴰ⇒cᴰ'⟩ expⱽ {f = λf×id}

--           p : ((C.id C.⋆ bp.π₁ bp.,p (C.id C.⋆ λf×id C.⋆ bp.π₂)) C.⋆ f) ≡ ((C.id C.⋆ λf×id) C.⋆ c⇒d.app)
--           p =
--             cong (C._⋆ f) (cong₂ bp._,p_ (C.⋆IdL _) (C.⋆IdL _))
--             ∙ cong₂ C._⋆_ (bp.,p≡ (sym $ C.⋆IdL _) (bp.×β₂ ∙ (sym $ C.⋆IdL _))) refl
--             ∙ C.⋆IdL _
--             ∙ sym c⇒d.⇒ue.β
--             ∙ cong₂ C._⋆_ (sym (C.⋆IdL _)) refl

--           hᴰ : Cᴰ.Hom[ C.id ][ isFib.f*yᴰ xᴰ bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ (isFib.f*yᴰ cᴰ bp.π₂) λf×id , isFib.f*yᴰ (isFib.f*yᴰ dᴰ c⇒d.app) λf×id ]
--           hᴰ = isFib.introCL (isFib.introCL (Cᴰ.reind p $ (((bpⱽ.π₁ Cᴰ.⋆ᴰ isFib.π) bpᴰ.,pᴰ (bpⱽ.π₂ Cᴰ.⋆ᴰ isFib.π Cᴰ.⋆ᴰ isFib.π)) Cᴰ.⋆ᴰ fᴰ)))

--           gᴰ : Cᴰ.Hom[ λf×id ][ isFib.f*yᴰ xᴰ bp.π₁ , expⱽ .vertex ]
--           gᴰ = ⟨λf×id⟩*⟨cᴰ⇒dᴰ⟩.lda hᴰ Cᴰ.⋆ⱽᴰ isFib.π
--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.rightInv f fᴰ =
--           Cᴰ.rectify $ Cᴰ.≡out $
--             Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ bpⱽ.⟨ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ∙ refl ⟩ ⟩,ⱽ⟨ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler (sym $ -×c.×aF .Functor.F-id) _ ⟩ ⟩ ⟩⋆⟨ refl ⟩ ⟩
--             ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
--             ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
--             ∙ Cᴰ.⟨ Cᴰ.⟨ Cᴰ.⟨ {!!} ⟩⋆⟨ {!!} ⟩ ⟩⋆⟨ {!!} ⟩ ∙ {!!} ∙ isFib.introCL⟨ {!!} ⟩⟨ {!!} ⟩ ⟩⋆⟨ refl ⟩
--             ∙ isFib.βCL
--             ∙ {!!}
--             -- ∙ (sym $ Cᴰ.reind-filler (sym $ C.⋆IdL _) _)

--             -- Cᴰ.⟨ bpⱽ.⟨ isFib.introCL⟨ refl ⟩⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ refl ⟩ ⟩⋆⟨
--             --   uq.lda≡ {!!} {!!} ⟩ ∙ {!!} ⟩ ⟩,ⱽ⟨ isFib.introCL⟨ {!!} ⟩⟨ (sym $ Cᴰ.reind-filler _ _) ∙ {!!} ⟩ ⟩ ⟩⋆⟨ refl ⟩
--             -- ∙ Cᴰ.⟨ bpⱽ.⟨ isFib.introCL⟨ {!!} ⟩⟨ {!!} ⟩ ⟩,ⱽ⟨ {!!} ⟩ ⟩⋆⟨ refl ⟩
--             -- ∙ {!!}
--           where
--           λf×id = -×c.×aF ⟪ c⇒d.lda f ⟫
--           module ⟨λf×id⟩*⟨cᴰ⇒dᴰ⟩ = f*⟨cᴰ⇒cᴰ'⟩ expⱽ {f = λf×id}
--         Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.leftInv = {!!}
