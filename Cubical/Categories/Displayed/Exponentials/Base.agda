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

      opaque
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

      opaque
        unfolding lda app
        β⇒ⱽ :
          ∀ {Γ}{f : C [ Γ , c ]}{Γᴰ}
          → {fᴰ : Cᴰ.Hom[ f ][ Γᴰ ×ⱽ isFib.f*yᴰ cᴰ f , cᴰ' ]}
          → Path Cᴰ.Hom[ _ , _ ]
          -- bpⱽ.BinProductFⱽ .F-homᴰ ((lda fᴰ) , isFib.π)
              (_ , (lda fᴰ bpⱽ.×p isFib.π) Cᴰ.⋆ᴰ app)
              (_ , fᴰ)
        β⇒ⱽ =
          Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _
            ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _)
              ∙ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _)
                           ∙ Cᴰ.⟨ (sym $ Cᴰ.reind-filler _ _) ⟩⋆⟨ refl ⟩
                           ∙ Cᴰ.⋆Assoc _ _ _
                           ∙ Cᴰ.⟨ refl ⟩⋆⟨ isFib.βCL ∙ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩
                           ∙ (sym $ Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ isFib.βCL ⟩⋆⟨ refl ⟩ ⟩ ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩
          ∙ sym (Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural
            ∙ bpⱽ.,ⱽ≡
                (((sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₁' ⟩⋆⟨ refl ⟩) ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ ,ⱽ≡
                       (sym (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ bpⱽ.×βⱽ₁' ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₁' ∙ sym (Cᴰ.reind-filler _ _) ⟩⋆⟨ refl ⟩ ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩) ∙ Cᴰ.reind-filler _ _)
                       (sym (sym (Cᴰ.reind-filler _ _)
                            ∙ Cᴰ.⋆Assoc _ _ _
                            ∙ Cᴰ.⟨ refl ⟩⋆⟨ bpⱽ.×βⱽ₂' ⟩
                            ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₂' ⟩⋆⟨ refl ⟩))
                   ⟩⋆⟨ isFib.βCL ∙ (sym $ Cᴰ.reind-filler _ _) ⟩) ∙ Cᴰ.reind-filler _ _)
                ((sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₂' ∙ isFib.introCL-natural ⟩⋆⟨ refl ⟩ ∙ isFib.βCL ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ bpⱽ.×βⱽ₂' ∙ sym (Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⟨ refl ⟩⋆⟨ bpⱽ.×βⱽ₂' ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₂' ⟩⋆⟨ refl ⟩))
                ∙ Cᴰ.reind-filler _ _)
            ⟩⋆⟨ refl ⟩
          ∙ Cᴰ.⋆Assoc _ _ _
          -- (_ ,ⱽ _) ⋆ᴰ introCL
          ∙ Cᴰ.⟨ refl ⟩⋆⟨ (Cᴰ.⟨ sym $ isFib.βCL ⟩⋆⟨ refl ⟩ ∙ Cᴰ.⋆Assoc _ _ _) ∙ (Cᴰ.⟨ refl ⟩⋆⟨ (Cᴰ.reind-filler _ _ ∙ sym (Cᴰ.⋆IdL _)) ∙ sym isFib.βCL ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _)) ∙ Cᴰ.⟨ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩ ⟩
          ∙ (sym $ Cᴰ.⋆Assoc _ _ _)
          ∙ Cᴰ.⟨ (refl ∙ Cᴰ.reind-filler _ _) ∙ (Cᴰ.≡in $ f*⟨cᴰ⇒cᴰ'⟩.⇒ue.β) ⟩⋆⟨ refl ⟩
          ∙ isFib.βⱽCL

        lda≡' :
          ∀ {Γ}{Γᴰ}{f : C [ Γ , c ]}{g : C [ Γ , c ]}
          → {fᴰ : Cᴰ.Hom[ f ][ Γᴰ ×ⱽ isFib.f*yᴰ cᴰ f , cᴰ' ]}
          → {gᴰ : Cᴰ.Hom[ g ][ Γᴰ , vertex ]}
          → (f≡g : f ≡ g)
          → Path Cᴰ.Hom[ _ , _ ]
              (_ , fᴰ)
              (_ , ((gᴰ bpⱽ.×p Cᴰ.reind f≡g isFib.π) Cᴰ.⋆ᴰ app))
          → Path Cᴰ.Hom[ _ , _ ]
              (_ , lda fᴰ)
              (_ , gᴰ)
        lda≡' f≡g fᴰ≡gᴰapp =
          sym (Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ (Cᴰ.≡in $ f*⟨cᴰ⇒cᴰ'⟩.⇒ue.intro≡ (Cᴰ.rectify $ Cᴰ.≡out $
            isFib.introCL≡ (sym (Cᴰ.reind-filler _ _)
              ∙ sym (isFib.βCL ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ (sym $ Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.⋆IdL _ ∙ (sym $ Cᴰ.reind-filler _ _) ⟩ ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ isFib.βCL ⟩⋆⟨ refl ⟩ ⟩
                ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩
                ∙ ((Cᴰ.⟨ ,ⱽ≡
                         (sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ bpⱽ.×βⱽ₁' ∙ sym (Cᴰ.reind-filler _ _) ∙ isFib.introCL-natural ⟩⋆⟨ refl ⟩
                         ∙ (isFib.βCL ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ sym
                           (Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩ ∙ bpⱽ.×βⱽ₁'
                           ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩ ∙ bpⱽ.×βⱽ₁' ∙ isFib.introCL-natural ⟩⋆⟨ refl ⟩ ∙ isFib.βCL ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ ×βⱽ₁' ))
                         ∙ Cᴰ.reind-filler _ _)
                         (sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ ×βⱽ₂' ∙ refl ⟩⋆⟨ refl ⟩ ∙ (sym $
                           sym (Cᴰ.reind-filler _ _ ) ∙ Cᴰ.⟨  bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩ ∙ ×βⱽ₂'
                           ∙ sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ Cᴰ.⟨ bpⱽ.×ueⱽ.∫ue.intro-natural ⟩⋆⟨ refl ⟩ ∙ ×βⱽ₂' ∙ isFib.introCL-natural ⟩⋆⟨ refl ⟩ ∙ isFib.βCL ∙ sym (Cᴰ.reind-filler _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩ ∙ ×βⱽ₂' ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym $ Cᴰ.reind-filler _ _ ⟩))
                     ⟩⋆⟨ refl ⟩ ∙ Cᴰ.⋆Assoc _ _ _ ∙ Cᴰ.⋆Assoc _ _ _ ) ∙ Cᴰ.⟨ refl ∙ Cᴰ.reind-filler _ _ ⟩⋆⟨ Cᴰ.⟨ refl ⟩⋆⟨ (((((Cᴰ.⟨ sym isFib.βCL ⟩⋆⟨ refl ⟩ ∙ Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ refl ⟩⋆⟨ Cᴰ.reind-filler _ _ ∙ sym (Cᴰ.⋆IdL _) ⟩) ∙ Cᴰ.reind-filler _ _) ∙ sym isFib.βCL) ∙ Cᴰ.⟨ sym isFib.introCL-natural ∙ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩) ∙ Cᴰ.reind-filler _ _ ⟩ ∙ Cᴰ.reind-filler _ _ ⟩)
                ∙ sym fᴰ≡gᴰapp)
              ∙ Cᴰ.⟨ (sym isFib.introCL-natural ∙ Cᴰ.⟨ refl ⟩⋆⟨ sym isFib.introCL-natural ∙ Cᴰ.reind-filler _ _ ⟩) ∙ Cᴰ.reind-filler _ _ ⟩⋆⟨ refl ⟩)))
               ⟩⋆⟨ refl ⟩
          ∙ isFib.βCL ∙ sym (Cᴰ.reind-filler (sym $ C.⋆IdL _ ∙ f≡g) _)
          -- ΣPathP (f≡g ,
          -- (Cᴰ.rectify $ {!f*⟨cᴰ⇒cᴰ'⟩.⇒ue.intro≡!}))

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
