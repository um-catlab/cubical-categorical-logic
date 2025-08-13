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

      -- TODO finish this exponential structure
      ⟨cᴰ⇒cᴰ'⟩ : Exponential Cᴰ.v[ c ] cᴰ cᴰ'
                   (BinProductsWithⱽ→BinProductsWithFiber Cᴰ (λ cᴰ'' → bpⱽ c (cᴰ'' , cᴰ)))
      ⟨cᴰ⇒cᴰ'⟩ .UniversalElement.vertex = vertex
      ⟨cᴰ⇒cᴰ'⟩ .UniversalElement.element = {!!}
      ⟨cᴰ⇒cᴰ'⟩ .UniversalElement.universal = {!!}
        -- CatIso→UniversalElement
        --   (record { vertex = isFib.f*yᴰ vertex C.id
        --           ; element = ((π₁ Cᴰ.⋆ⱽ isFib.π) ,ⱽ π₂) Cᴰ.⋆ⱽ element
        --           ; universal = λ cᴰ'' →
        --             isIsoToIsEquiv (
        --               (λ fⱽ → f*⟨cᴰ⇒cᴰ'⟩.lda (
        --                  (π₁ ,ⱽ (π₂ Cᴰ.⋆ⱽ isFib.π)) Cᴰ.⋆ⱽ (fⱽ Cᴰ.⋆ⱽ id*≅-ob' Cᴰ isFib .snd .isIso.inv))) ,
        --               (λ fⱽ → Cᴰ.rectify $ Cᴰ.≡out $
        --                 (sym $ Cᴰ.reind-filler _ _)
        --                 ∙ Cᴰ.⟨ ⟨ (sym $ Cᴰ.reind-filler _ _)
        --                        ∙ Cᴰ.⟨ refl ⟩⋆⟨
        --                         lda≡ refl
        --                           ((sym $ Cᴰ.reind-filler _ _)
        --                           ∙ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _)
        --                                          ∙ Cᴰ.⟨ refl ⟩⋆⟨ isFib.introCL⟨ refl ⟩⟨ refl ⟩ ⟩ ⟩
        --                           ∙ {!!}
        --                           )
        --                           ⟩ ⟩,ⱽ⟨ (Cᴰ.reind-filler (sym $ C.⋆IdR _) _) ⟩ ⟩⋆⟨ refl ⟩
        --                 ∙ {!!}
        --               ) ,
        --               {!!})
        --    })
        --   (id*≅-ob' Cᴰ isFib {xᴰ = vertex})
      module ⟨cᴰ⇒cᴰ'⟩ = ExponentialNotation _ ⟨cᴰ⇒cᴰ'⟩

    Exponentialsⱽ : Type _
    Exponentialsⱽ = ∀ {c} cᴰ cᴰ' → Exponentialⱽ {c} cᴰ cᴰ'

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

      open Exponentialⱽ
      open UniversalElementᴰ
      open UniversalElementⱽ

      module _
        (uq : UniversalQuantifier (λ c' → bp (c' , c)) isFib (expⱽ .vertex))
        where

        module uq = UniversalQuantifierNotation _ isFib uq

        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ :
          Exponentialᴰ Cᴰ cᴰ dᴰ (λ c' cᴰ' → bpᴰ (cᴰ' , cᴰ)) exp
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .vertexᴰ = uq.vert
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ  .elementᴰ = the-elt
          where
          fᴰ : Cᴰ [ C.id ][ isFib.f*yᴰ (uq .vertexⱽ) bp.π₁ , expⱽ .vertex ]
          fᴰ = Cᴰ.reind (-×c.×aF .Functor.F-id) $ uq.app

          gᴰ : Cᴰ [ _ C.⋆ _ C.⋆ c⇒d.app ][ isFib.f*yᴰ (uq .vertexⱽ) bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
          gᴰ = ((bpⱽ.π₁ Cᴰ.⋆ᴰ fᴰ) bpⱽ.,ⱽ (bpⱽ.π₂ Cᴰ.⋆ᴰ Cᴰ.idᴰ)) Cᴰ.⋆ᴰ expⱽ .element Cᴰ.⋆ᴰ isFib.π

          the-elt : Cᴰ [ c⇒d.app ][ isFib.f*yᴰ uq.vert bp.π₁ bpⱽ.×ⱽ isFib.f*yᴰ cᴰ bp.π₂ , dᴰ ]
          the-elt =
            Cᴰ.reind
              ((λ i → C.⋆IdL C.id i C.⋆ C.id C.⋆ c⇒d.app)
              ∙ C.⋆IdL _
              ∙ C.⋆IdL _)
              gᴰ
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.inv f fᴰ =
          uq.lda (Cᴰ.reind {!!} $
            f*⟨cᴰ⇒cᴰ'⟩.lda expⱽ {f = -×c.×aF ⟪ c⇒d.lda f ⟫}
              {!!} Cᴰ.⋆ᴰ isFib.π)
          -- uq.lda (Cᴰ.reind {!!} $ (isFib.f*F {!f!} ⟪ {!fᴰ!} ⟫ Cᴰ.⋆ᴰ {!!}) Cᴰ.⋆ᴰⱽ ⟨cᴰ⇒cᴰ'⟩.lda expⱽ bpⱽ.π₁)
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.rightInv = {!!}
        Exponentialⱽ+UniversalQuanitier→Exponentialᴰ .universalᴰ .isIsoOver.leftInv = {!!}
