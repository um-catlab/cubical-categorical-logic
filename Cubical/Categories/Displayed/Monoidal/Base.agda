-- Displayed monoidal categories

module Cubical.Categories.Displayed.Monoidal.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Properties
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory as TotalCategory
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Morphism
open import Cubical.Categories.NaturalTransformation.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓM ℓM' ℓMᴰ ℓMᴰ' : Level
open Functorᴰ
open NatIsoᴰ
open NatTransᴰ
open isIsoᴰ
module _ (M : MonoidalCategory ℓM ℓM') where
  private
    module M = MonoidalCategory M
  module _ (Cᴰ : Categoryᴰ M.C ℓMᴰ ℓMᴰ') where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    record TensorStrᴰ : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')) where
      field
        ─⊗ᴰ─ : Functorᴰ M.─⊗─ (Cᴰ ×Cᴰ Cᴰ) Cᴰ
        unitᴰ : Cᴰ.ob[ M.unit ]
      _⊗ᴰ_ : ∀ {x y} → Cᴰ.ob[ x ] → Cᴰ.ob[ y ] → Cᴰ.ob[ x M.⊗ y ]
      xᴰ ⊗ᴰ yᴰ = ─⊗ᴰ─ .F-obᴰ (xᴰ , yᴰ)

      _⊗ₕᴰ_ : ∀ {x y z w}{xᴰ yᴰ zᴰ wᴰ}{f : M.C [ x , y ]}{g : M.C [ z , w ]}
        → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
        → Cᴰ.Hom[ g ][ zᴰ , wᴰ ]
        → Cᴰ.Hom[ f M.⊗ₕ g ][ xᴰ ⊗ᴰ zᴰ , yᴰ ⊗ᴰ wᴰ ]
      fᴰ ⊗ₕᴰ gᴰ = ─⊗ᴰ─ .F-homᴰ (fᴰ , gᴰ)

    record MonoidalStrᴰ : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')) where
      field
        tenstrᴰ : TensorStrᴰ
      open TensorStrᴰ tenstrᴰ public
      field
        αᴰ : NatIsoᴰ M.α
               (─⊗ᴰ─ ∘Fᴰ (𝟙ᴰ⟨ Cᴰ ⟩ ×Fᴰ ─⊗ᴰ─))
               (─⊗ᴰ─ ∘Fᴰ ((─⊗ᴰ─ ×Fᴰ 𝟙ᴰ⟨ Cᴰ ⟩) ∘Fᴰ ×Cᴰ-assoc Cᴰ Cᴰ Cᴰ))
        ηᴰ : NatIsoᴰ M.η
               (─⊗ᴰ─ ∘Fᴰ rinjᴰ Cᴰ Cᴰ unitᴰ)
               𝟙ᴰ⟨ Cᴰ ⟩
        ρᴰ : NatIsoᴰ M.ρ
               (─⊗ᴰ─ ∘Fᴰ linjᴰ Cᴰ Cᴰ unitᴰ)
               𝟙ᴰ⟨ Cᴰ ⟩
      αᴰ⟨_,_,_⟩ : ∀ {x y z} xᴰ yᴰ zᴰ
        → Cᴰ.Hom[ M.α⟨ x , y , z ⟩ ][ xᴰ ⊗ᴰ (yᴰ ⊗ᴰ zᴰ) , (xᴰ ⊗ᴰ yᴰ) ⊗ᴰ zᴰ ]
      αᴰ⟨ xᴰ , yᴰ , zᴰ ⟩ = αᴰ .transᴰ .N-obᴰ (xᴰ , yᴰ , zᴰ)

      α⁻¹ᴰ⟨_,_,_⟩ : ∀ {x y z} xᴰ yᴰ zᴰ
        → Cᴰ.Hom[ M.α⁻¹⟨ x , y , z ⟩ ][ (xᴰ ⊗ᴰ yᴰ) ⊗ᴰ zᴰ , xᴰ ⊗ᴰ (yᴰ ⊗ᴰ zᴰ) ]
      α⁻¹ᴰ⟨ xᴰ , yᴰ , zᴰ ⟩ = αᴰ .nIsoᴰ (xᴰ , yᴰ , zᴰ) .invᴰ

      ηᴰ⟨_⟩ : ∀ {x} xᴰ
        → Cᴰ.Hom[ M.η⟨ x ⟩ ][ unitᴰ ⊗ᴰ xᴰ , xᴰ ]
      ηᴰ⟨ xᴰ ⟩ = ηᴰ .transᴰ .N-obᴰ xᴰ

      η⁻¹ᴰ⟨_⟩ : ∀ {x} xᴰ
        → Cᴰ.Hom[ M.η⁻¹⟨ x ⟩ ][ xᴰ , unitᴰ ⊗ᴰ xᴰ ]
      η⁻¹ᴰ⟨ xᴰ ⟩ = ηᴰ .nIsoᴰ xᴰ .invᴰ

      ρᴰ⟨_⟩ : ∀ {x} xᴰ
        → Cᴰ.Hom[ M.ρ⟨ x ⟩ ][ xᴰ ⊗ᴰ unitᴰ , xᴰ ]
      ρᴰ⟨ xᴰ ⟩ = ρᴰ .transᴰ .N-obᴰ xᴰ

      ρ⁻¹ᴰ⟨_⟩ : ∀ {x} xᴰ
        → Cᴰ.Hom[ M.ρ⁻¹⟨ x ⟩ ][ xᴰ , xᴰ ⊗ᴰ unitᴰ ]
      ρ⁻¹ᴰ⟨ xᴰ ⟩ = ρᴰ .nIsoᴰ xᴰ .invᴰ

      field
        pentagonᴰ :
          ∀ {w x y z} wᴰ xᴰ yᴰ zᴰ
          → ((Cᴰ.idᴰ ⊗ₕᴰ αᴰ⟨ xᴰ , yᴰ , zᴰ ⟩)
              Cᴰ.⋆ᴰ αᴰ⟨ _ , _ , _ ⟩
              Cᴰ.⋆ᴰ (αᴰ⟨ wᴰ , xᴰ , yᴰ ⟩ ⊗ₕᴰ Cᴰ.idᴰ))
              Cᴰ.≡[ M.pentagon w x y z ]
            (αᴰ⟨ _ , _ , _ ⟩ Cᴰ.⋆ᴰ αᴰ⟨ _ , _ , _ ⟩)
        triangleᴰ : ∀ {x y} xᴰ yᴰ
          → (αᴰ⟨ xᴰ , unitᴰ , yᴰ ⟩ Cᴰ.⋆ᴰ (ρᴰ⟨ xᴰ ⟩ ⊗ₕᴰ Cᴰ.idᴰ))
              Cᴰ.≡[ M.triangle x y ]
            (Cᴰ.idᴰ ⊗ₕᴰ ηᴰ⟨ yᴰ ⟩)

    record MonoidalPropᴰ : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')) where
      field
        tenstrᴰ : TensorStrᴰ
      open TensorStrᴰ tenstrᴰ public
      field
        αᴰ⟨_,_,_⟩ : ∀ {x y z} xᴰ yᴰ zᴰ
          → Cᴰ.Hom[ M.α⟨ x , y , z ⟩ ][ xᴰ ⊗ᴰ (yᴰ ⊗ᴰ zᴰ) , (xᴰ ⊗ᴰ yᴰ) ⊗ᴰ zᴰ ]
        α⁻¹ᴰ⟨_,_,_⟩ : ∀ {x y z} xᴰ yᴰ zᴰ
          → Cᴰ.Hom[ M.α⁻¹⟨ x , y , z ⟩ ][ (xᴰ ⊗ᴰ yᴰ) ⊗ᴰ zᴰ , xᴰ ⊗ᴰ (yᴰ ⊗ᴰ zᴰ) ]

        ηᴰ⟨_⟩ : ∀ {x} xᴰ
          → Cᴰ.Hom[ M.η⟨ x ⟩ ][ unitᴰ ⊗ᴰ xᴰ , xᴰ ]
        η⁻¹ᴰ⟨_⟩ : ∀ {x} xᴰ
          → Cᴰ.Hom[ M.η⁻¹⟨ x ⟩ ][ xᴰ , unitᴰ ⊗ᴰ xᴰ ]

        ρᴰ⟨_⟩ : ∀ {x} xᴰ
          → Cᴰ.Hom[ M.ρ⟨ x ⟩ ][ xᴰ ⊗ᴰ unitᴰ , xᴰ ]
        ρ⁻¹ᴰ⟨_⟩ : ∀ {x} xᴰ
          → Cᴰ.Hom[ M.ρ⁻¹⟨ x ⟩ ][ xᴰ , xᴰ ⊗ᴰ unitᴰ ]

    TensorPropᴰ→TensorStrᴰ : hasPropHoms Cᴰ → MonoidalPropᴰ → MonoidalStrᴰ
    TensorPropᴰ→TensorStrᴰ isPropHomᴰ TP = record
      { tenstrᴰ = TP.tenstrᴰ
      ; αᴰ = mkNatIsoPropHom M.α _ _ isPropHomᴰ
             (λ xᴰ → TP.αᴰ⟨ _ , _ , _ ⟩) λ xᴰ → TP.α⁻¹ᴰ⟨ _ , _ , _ ⟩
      ; ηᴰ = mkNatIsoPropHom M.η _ _ isPropHomᴰ
             (λ xᴰ → TP.ηᴰ⟨ _ ⟩) λ xᴰ → TP.η⁻¹ᴰ⟨ _ ⟩
      ; ρᴰ = mkNatIsoPropHom M.ρ _ _ isPropHomᴰ
             (λ xᴰ → TP.ρᴰ⟨ _ ⟩) λ xᴰ → TP.ρ⁻¹ᴰ⟨ _ ⟩
      ; pentagonᴰ = λ wᴰ xᴰ yᴰ zᴰ → propHomsFiller Cᴰ isPropHomᴰ _ _ _
      ; triangleᴰ = λ xᴰ yᴰ → propHomsFiller Cᴰ isPropHomᴰ _ _ _
      }
      where
        module TP = MonoidalPropᴰ TP
  record MonoidalCategoryᴰ ℓMᴰ ℓMᴰ'
    : Type ((ℓ-suc (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓMᴰ ℓMᴰ')))) where
    field
      Cᴰ : Categoryᴰ M.C ℓMᴰ ℓMᴰ'
      monstrᴰ : MonoidalStrᴰ Cᴰ
    -- Probably a bad idea
    open Fibers Cᴰ public
    open MonoidalStrᴰ monstrᴰ public

    open MonoidalCategory
    open MonoidalStr
    open TensorStr
    open Functor
    open NatIso
    open NatTrans
    open isIso
    -- Probably some combinators we could use here rather than doing this all manually
    ∫ : MonoidalCategory (ℓ-max ℓM ℓMᴰ) (ℓ-max ℓM' ℓMᴰ')
    ∫ .MonoidalCategory.C = ∫C Cᴰ
    ∫ .monstr .tenstr .─⊗─ =
      TotalCategory.intro {C = M.C}{Cᴰ = Cᴰ}
        (M.─⊗─ ∘F (TotalCategory.Fst {C = M.C}{Cᴰ = Cᴰ} ×F TotalCategory.Fst {C = M.C}{Cᴰ = Cᴰ}))
        (compFunctorᴰSection ─⊗ᴰ─ (TotalCategory.Snd ×Sᴰ TotalCategory.Snd))
    ∫ .monstr .tenstr .unit = M.unit , unitᴰ
    -- TODO: less manual version of this
    ∫ .monstr .α .trans .N-ob ((_ , x), (_ , y), (_ , z)) = _ , αᴰ⟨ x , y , z ⟩
    ∫ .monstr .α .trans .N-hom ((_ , f), (_ , g), (_ , h)) = ΣPathP (_ , αᴰ .transᴰ .N-homᴰ (f , g , h))
    ∫ .monstr .α .nIso ((_ , x) , (_ , y) , _ , z) .inv = _ , α⁻¹ᴰ⟨ x , y , z ⟩
    ∫ .monstr .α .nIso ((_ , x) , (_ , y) , _ , z) .sec = ΣPathP (_ , αᴰ .nIsoᴰ (x , y , z) .secᴰ)
    ∫ .monstr .α .nIso ((_ , x) , (_ , y) , _ , z) .ret = ΣPathP (_ , αᴰ .nIsoᴰ (x , y , z) .retᴰ)
    ∫ .monstr .ρ .trans .N-ob (_ , x) = _ , ρᴰ⟨ x ⟩
    ∫ .monstr .ρ .trans .N-hom (_ , f) = ΣPathP (_ , ρᴰ .transᴰ .N-homᴰ f)
    ∫ .monstr .ρ .nIso (_ , x) .inv = _ , ρ⁻¹ᴰ⟨ x ⟩
    ∫ .monstr .ρ .nIso (_ , x) .sec = ΣPathP (_ , ρᴰ .nIsoᴰ x .secᴰ)
    ∫ .monstr .ρ .nIso (_ , x) .ret = ΣPathP (_ , ρᴰ .nIsoᴰ x .retᴰ)
    ∫ .monstr .η .trans .N-ob (_ , x) = _ , ηᴰ⟨ x ⟩
    ∫ .monstr .η .trans .N-hom (_ , f) = ΣPathP (_ , ηᴰ .transᴰ .N-homᴰ f)
    ∫ .monstr .η .nIso (_ , x) .inv = _ , η⁻¹ᴰ⟨ x ⟩
    ∫ .monstr .η .nIso (_ , x) .sec = ΣPathP (_ , ηᴰ .nIsoᴰ x .secᴰ)
    ∫ .monstr .η .nIso (_ , x) .ret = ΣPathP (_ , ηᴰ .nIsoᴰ x .retᴰ)
    ∫ .monstr .pentagon (_ , w) (_ , x) (_ , y) (_ , z) = ΣPathP (_ , pentagonᴰ w x y z)
    ∫ .monstr .triangle (_ , x) (_ , y) = ΣPathP (_ , triangleᴰ x y)

    module ∫ = MonoidalCategoryNotation ∫
