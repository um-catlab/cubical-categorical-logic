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
open import Cubical.Foundations.Equiv
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
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Presheaf

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
        f*⟨cᴰ⇒cᴰ'⟩ : Exponential Cᴰ.v[ b ] (isFib.f*yᴰ cᴰ f) (isFib.f*yᴰ cᴰ' f) (BinProductsWithⱽ→BinProductsWithFiber Cᴰ (λ cᴰ'' → bpⱽ _ _))
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

    Exponentialsⱽ : Type _
    Exponentialsⱽ = ∀ {c} cᴰ cᴰ' → Exponentialⱽ {c} cᴰ cᴰ'
