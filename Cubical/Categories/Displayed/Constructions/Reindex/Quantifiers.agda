{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
{-
  Sufficient conditions for Reindexed displayed category to have (universal) quantifiers
-}
module Cubical.Categories.Displayed.Constructions.Reindex.Quantifiers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {c : C .Category.ob}
  (-×c : BinProductsWith C c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  (F-× : preservesProvidedBinProductsWith F -×c)
  (isFibDᴰ : isFibration Dᴰ)
  where

  private
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module C = Category C
    module D = Category D
    module Dᴰ = Fibers Dᴰ
    module F*Dᴰ = Fibers (Base.reindex Dᴰ F)
    module isFibDᴰ = isFibrationNotation _ isFibDᴰ
    isFibF*Dᴰ = isFibrationReindex Dᴰ F isFibDᴰ
    module isFibF*Dᴰ = isFibrationNotation _ isFibF*Dᴰ
    module F⟨-×c⟩ {Γ} = BinProductNotation (preservesUniversalElement→UniversalElement (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))
  module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
    module F⟨Γ×c⟩ = BinProductNotation (preservesUniversalElement→UniversalElement (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

    module _ (∀dᴰ : UniversalQuantifier -×Fc isFibDᴰ
                  (isFibDᴰ.f*yᴰ dᴰ (-×Fc.π₁ F⟨Γ×c⟩.,p -×Fc.π₂))) where
      private
        module ∀dᴰ = UniversalQuantifierNotation _ _ ∀dᴰ
      open UniversalElementⱽ
      open Functor
      open Functorᴰ
      -- A lot of the below should probably be general facts about
      -- preservation of products?
      private
        ∀Reindex-vert : F*Dᴰ.ob[ Γ ]
        ∀Reindex-vert = ∀dᴰ.vert

        opaque
          ∀Reindex-elt-reind : ∀ {Δ} →
            (F⟨-×c⟩.π₁ -×Fc.,p F⟨-×c⟩.π₂)
             D.⋆ -×Fc.×aF ⟪ D.id ⟫
             D.⋆ (-×Fc.π₁ F⟨-×c⟩.,p -×Fc.π₂)
            ≡ F ⟪ -×c.×aF ⟪ C.id {Δ} ⟫ ⟫
          ∀Reindex-elt-reind = (D.⟨ refl ⟩⋆⟨ D.⟨ -×Fc.×aF .F-id ⟩⋆⟨ refl ⟩ ∙ D.⋆IdL _ ⟩
            ∙ F⟨-×c⟩.×ue.intro-natural
            ∙ F⟨-×c⟩.⟨ -×Fc.×β₁ ⟩,p⟨ -×Fc.×β₂ ⟩
            ∙ (sym $ F⟨-×c⟩.×ue.weak-η)
            ∙ (sym $ F .F-id) ∙ cong (F .F-hom) (sym $ -×c.×aF .F-id))

        -- TODO: make the reind pfs here into lemmas
        ∀Reindex-elt : Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ Category.id C ⟫ ⟫
          ][ isFibDᴰ.f*yᴰ ∀dᴰ.vert (F ⟪ -×c.π₁ ⟫)
          , dᴰ ]
        ∀Reindex-elt = Dᴰ.reind ∀Reindex-elt-reind $
          isFibDᴰ.introCL (Dᴰ.reind (sym $ -×Fc.×β₁) $
            isFibF*Dᴰ.π )
          Dᴰ.⋆ᴰ ∀dᴰ.app
          Dᴰ.⋆ᴰ isFibDᴰ.π

        opaque
          ∀Reindex-intro-reind : ∀ {Δ}{γ : C [ Δ , Γ ]} →
            (-×Fc.π₁ F⟨-×c⟩.,p -×Fc.π₂) D.⋆ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫
            ≡ -×Fc.×aF ⟪ F ⟪ γ ⟫ ⟫ D.⋆ (-×Fc.π₁ F⟨Γ×c⟩.,p -×Fc.π₂)
          ∀Reindex-intro-reind = sym (F⟨Γ×c⟩.,p≡
              (-×Fc.×β₁ ∙ D.⟨ sym F⟨-×c⟩.×β₁ ⟩⋆⟨ refl ⟩ ∙ D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) (sym -×c.×β₁) ∙ F .F-seq _ _ ⟩ ∙ sym (D.⋆Assoc _ _ _))
              (-×Fc.×β₂ ∙ sym F⟨-×c⟩.×β₂ ∙ D.⟨ refl ⟩⋆⟨ cong (F .F-hom) (sym -×c.×β₂) ∙ F .F-seq _ _ ⟩ ∙ sym (D.⋆Assoc _ _ _)))
            ∙ (sym $ F⟨Γ×c⟩.×ue.intro-natural)

        ∀Reindex-intro' :
          ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]} →
          Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ F⟨-×c⟩.π₁ , dᴰ ]
          → Dᴰ [ -×Fc.×aF ⟪ F ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ -×Fc.π₁
                                      , isFibDᴰ.f*yᴰ dᴰ (-×Fc.π₁ F⟨Γ×c⟩.,p -×Fc.π₂) ]
        ∀Reindex-intro' γᴰ = isFibDᴰ.introCL $
          Dᴰ.reind ∀Reindex-intro-reind $
            (isFibDᴰ.introCL $ Dᴰ.reind
              (sym $ F⟨-×c⟩.×β₁) $
              isFibDᴰ.π)
            Dᴰ.⋆ᴰ γᴰ
        ∀Reindex-intro :
          ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]} →
          Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ F⟨-×c⟩.π₁ , dᴰ ]
          → Dᴰ.Hom[ F ⟪ γ ⟫ ][ Δᴰ , ∀dᴰ.∀ueⱽ.vertexⱽ ]
        ∀Reindex-intro γᴰ = ∀dᴰ.lda $ ∀Reindex-intro' γᴰ

        ∀Reindex-intro⁻ :
          ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
          → Dᴰ.Hom[ F ⟪ γ ⟫ ][ Δᴰ , ∀dᴰ.∀ueⱽ.vertexⱽ ]
          → Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ F⟨-×c⟩.π₁ , dᴰ ]
        ∀Reindex-intro⁻ γᴰ =
          (UniversalQuantifierPshⱽ -×c isFibF*Dᴰ dᴰ PresheafⱽNotation.⋆ᴰⱽ γᴰ) ∀Reindex-elt

        ∀Reindex-intro⁻'' :
          ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
          → Dᴰ.Hom[ F ⟪ γ ⟫ ][ Δᴰ , ∀dᴰ.∀ueⱽ.vertexⱽ ]
          → Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ F⟨-×c⟩.π₁ , dᴰ ]
        ∀Reindex-intro⁻'' γᴰ = Dᴰ.reind
          (D.⟨ refl ⟩⋆⟨ D.⟨ D.⟨ refl ⟩⋆⟨ -×Fc.×aF .F-id ⟩ ∙ D.⋆IdR _ ⟩⋆⟨ refl ⟩ ∙ F⟨Γ×c⟩.×ue.intro-natural ∙ F⟨Γ×c⟩.⟨ -×Fc.×β₁ ⟩,p⟨ -×Fc.×β₂ ⟩ ⟩
          ∙ F⟨-×c⟩.×ue.intro-natural ∙ F⟨-×c⟩.⟨ (sym $ D.⋆Assoc _ _ _) ∙ D.⟨ -×Fc.×β₁ ⟩⋆⟨ refl ⟩ ⟩,p⟨ -×Fc.×β₂ ⟩
          ∙ F⟨-×c⟩.,p≡
            (((sym $ F .F-seq _ _) ∙ cong (F .F-hom) (sym -×c.×β₁)) ∙ F .F-seq _ _)
            (cong (F .F-hom) (sym -×c.×β₂) ∙ F .F-seq _ _)) $
          isFibDᴰ.introCL (Dᴰ.reind (sym $ -×Fc.×β₁) $ isFibDᴰ.π)
          Dᴰ.⋆ᴰ (weakenⱽ -×Fc isFibDᴰ .F-homᴰ γᴰ Dᴰ.⋆ᴰ ∀dᴰ.∀ueⱽ.elementⱽ)
          Dᴰ.⋆ᴰ isFibDᴰ.π
        opaque
          ∀Reindex-intro⁻≡ : ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
            → (γᴰ : Dᴰ.Hom[ F ⟪ γ ⟫ ][ Δᴰ , ∀dᴰ.∀ueⱽ.vertexⱽ ])
            → ∀Reindex-intro⁻ γᴰ ≡ ∀Reindex-intro⁻'' γᴰ
          ∀Reindex-intro⁻≡ γᴰ = Dᴰ.rectify $ Dᴰ.≡out $
            (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
            ∙ (sym $ Dᴰ.⋆Assoc _ _ _)
            ∙ Dᴰ.⟨ isFibDᴰ.introCL-natural
                 ∙ isFibDᴰ.introCL⟨
                      -×Fc.×ue.intro-natural
                      ∙ -×Fc.⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) -×c.×β₁ ∙ F .F-seq _ _ ∙ D.⟨ sym -×Fc.×β₁ ⟩⋆⟨ refl ⟩ ∙ D.⋆Assoc _ _ _ ⟩,p⟨ sym (F .F-seq _ _) ∙ cong (F .F-hom) -×c.×β₂ ∙ sym -×Fc.×β₂ ⟩
                      ∙ sym -×Fc.×ue.intro-natural
                   ⟩⟨ (sym $ Dᴰ.reind-filler _ _)
                      ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩
                      ∙ isFibDᴰ.βCL ∙ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.reind-filler _ _)
                      ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ∙ (sym $ isFibDᴰ.βCL) ⟩⋆⟨ refl ⟩ ∙ Dᴰ.⋆Assoc _ _ _
                      ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩ ∙ Dᴰ.reind-filler _ _ ⟩
                 ∙ sym isFibDᴰ.introCL-natural
              ⟩⋆⟨ refl ⟩
            ∙ Dᴰ.⋆Assoc _ _ _
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.⋆Assoc _ _ _ ⟩
            ∙ Dᴰ.reind-filler _ _

          ∀Reindex-β : ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
            (γᴰ : Dᴰ.Hom[ F ⟪ -×c.×aF ⟪ γ ⟫ ⟫ ][ isFibDᴰ.f*yᴰ Δᴰ F⟨-×c⟩.π₁ , dᴰ ])
            → ∀Reindex-intro⁻ (∀Reindex-intro γᴰ) ≡ γᴰ
          ∀Reindex-β {Δ}{Δᴰ}{γ} γᴰ = ∀Reindex-intro⁻≡ _ ∙ (Dᴰ.rectify $ Dᴰ.≡out $
            sym (Dᴰ.reind-filler _ _)
            ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.⟨ ∀dᴰ.∀β {fᴰ = ∀Reindex-intro' γᴰ} ⟩⋆⟨ refl ⟩ ∙ isFibDᴰ.βCL ∙ (sym $ Dᴰ.reind-filler _ _) ⟩
            ∙ sym (Dᴰ.⋆Assoc _ _ _)
            ∙ Dᴰ.⟨ isFibDᴰ.introCL-natural
              ∙ isFibDᴰ.introCL≡'
                  (F⟨-×c⟩.,p-extensionality
                    (D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ F⟨-×c⟩.×β₁ ⟩ ∙ -×Fc.×β₁ ∙ (sym $ D.⋆IdL _))
                    (D.⋆Assoc _ _ _ ∙ D.⟨ refl ⟩⋆⟨ F⟨-×c⟩.×β₂ ⟩ ∙ -×Fc.×β₂ ∙ (sym $ D.⋆IdL _)))
                  ((sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ∙ isFibDᴰ.βCL ∙ sym (Dᴰ.reind-filler _ _) ∙ sym (Dᴰ.⋆IdL _) )
              ⟩⋆⟨ refl ⟩
            ∙ Dᴰ.⋆IdL _)

          ∀Reindex-η : ∀ {Δ}{Δᴰ}{γ : C [ Δ , Γ ]}
            (γᴰ : Dᴰ.Hom[ F ⟪ γ ⟫ ][ Δᴰ , ∀dᴰ.∀ueⱽ.vertexⱽ ])
            → ∀Reindex-intro (∀Reindex-intro⁻ γᴰ) ≡ γᴰ
          ∀Reindex-η γᴰ = cong ∀Reindex-intro (∀Reindex-intro⁻≡ γᴰ) ∙ (Dᴰ.rectify $ Dᴰ.≡out $ ∀dᴰ.lda≡ refl $
            (isFibDᴰ.introCL≡'
              (sym (D.⋆IdR _) ∙ D.⟨ refl ⟩⋆⟨ sym $ -×Fc.×aF .F-id ⟩)
              ( (sym $ Dᴰ.reind-filler _ _)
              ∙ Dᴰ.⟨ refl ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.⋆Assoc _ _ _ ⟩ ∙ sym (Dᴰ.⋆Assoc _ _ _) ⟩
              ∙ sym (Dᴰ.⋆Assoc _ _ _)
              -- introCL π ⋆ᴰ introCL π ⋆ᴰ introCL (π ⋆ᴰ γᴰ)
              -- ≡ intro (π ⋆ᴰ γᴰ)
              ∙ Dᴰ.⟨ sym (Dᴰ.⋆Assoc _ _ _)
                     -- introCL π ⋆ᴰ introCL π ≡ idᴰ
                     ∙ Dᴰ.⟨ isFibDᴰ.introCL-natural
                          ∙ isFibDᴰ.introCL≡'
                              (-×Fc.×ue.intro-natural ∙ -×Fc.⟨ F⟨-×c⟩.×β₁ ⟩,p⟨ F⟨-×c⟩.×β₂ ⟩ ∙ sym -×Fc.×ue.weak-η)
                              ((sym $ Dᴰ.reind-filler _ _) ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym $ Dᴰ.reind-filler _ _ ⟩ ∙ isFibDᴰ.βCL ∙ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.⋆IdL _))
                        ⟩⋆⟨ refl ⟩
                     ∙ Dᴰ.⋆IdL _
                 ⟩⋆⟨ refl ⟩
              ∙ sym (Dᴰ.⋆Assoc _ _ _))))

      ∀Reindex : UniversalQuantifier -×c isFibF*Dᴰ dᴰ
      ∀Reindex .vertexⱽ = ∀Reindex-vert
      ∀Reindex .elementⱽ = ∀Reindex-elt
      ∀Reindex .universalⱽ .fst = ∀Reindex-intro
      ∀Reindex .universalⱽ .snd .fst = ∀Reindex-β
      ∀Reindex .universalⱽ .snd .snd = ∀Reindex-η

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {F : Functor C D}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {c : C .Category.ob}
  (bpC : BinProducts C)
  (bpD : BinProducts D)
  (F-× : preservesProvidedBinProducts F bpC)
  (isFibDᴰ : isFibration Dᴰ)
  where
  ∀sReindex : UniversalQuantifiers bpD isFibDᴰ
    → UniversalQuantifiers bpC (isFibrationReindex Dᴰ F isFibDᴰ)
  ∀sReindex ∀sD a Γ pᴰ =
    ∀Reindex
      (λ c₁ → bpC (c₁ , a))
      (λ c₁ → bpD (c₁ , Functor.F-ob F a))
      (λ c' → F-× c' a)
      isFibDᴰ
      (∀sD _ _ _)
