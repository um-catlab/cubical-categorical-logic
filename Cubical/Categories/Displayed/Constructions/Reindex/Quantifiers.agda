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
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.FunctorComprehension.Properties
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Base
open import Cubical.Categories.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.Displayed.Constructions.Reindex.Limits
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions.Quantifiers
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Functor
open Functorᴰ
open PshHom
open PshHomᴰ
open UniversalElementⱽ

module _
  {C : Category ℓC ℓC'}
  {D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {c : C .Category.ob}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (-×c : BinProductsWith C c)
  (-×Fc : BinProductsWith D (F ⟅ c ⟆))
  (F-× : preservesProvidedBinProductsWith F -×c)
  where

  private
    module C = Category C
    module D = Category D
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ
    F*Dᴰ = Base.reindex Dᴰ F
    module F*Dᴰ = Fibers F*Dᴰ
    module -×c = BinProductsWithNotation -×c
    module -×Fc = BinProductsWithNotation -×Fc
    module F-× = preservesProvidedBinProductsWithNotation F -×c -×Fc F-×
    module F⟨-×c⟩ {Γ} =
      BinProductNotation
        (preservesUniversalElement→UniversalElement
          (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

    module _ {Γ} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]} where
      module F⟨Γ×c⟩ =
        BinProductNotation
          (preservesUniversalElement→UniversalElement
            (preservesBinProdCones F Γ c) (-×c Γ) (F-× Γ))

  module _
    (π₁*C : ∀ {Γ} →
      (Γᴰ : Cᴰ.ob[ Γ ]) → CartesianLift Cᴰ Γᴰ -×c.π₁)
    (π₁*D : ∀ {Δ} →
      (Δᴰ : Dᴰ.ob[ Δ ]) → CartesianLift Dᴰ Δᴰ -×Fc.π₁)
    (isFibDᴰ : isFibration Dᴰ)
    where
    module _ {Γ : C.ob} {dᴰ : F*Dᴰ.ob[ Γ -×c.×a ]}
      (∀dᴰ : UniversalQuantifier -×Fc
               (λ Δᴰ → isFibDᴰ Δᴰ -×Fc.π₁)
               (isFibDᴰ dᴰ (-×Fc.π₁ F⟨-×c⟩.,p -×Fc.π₂) .vertexⱽ))
      where

      private
        module ∀ⱽDᴰ =
          UniversalQuantifierPsh {Cᴰ = Dᴰ} -×Fc
            (λ Dᴰ → isFibDᴰ Dᴰ -×Fc.π₁)
        ∀ⱽDᴰPsh = ∀ⱽDᴰ.∀ⱽPsh

      module ∀ⱽF*Dᴰ =
        UniversalQuantifierPsh {Cᴰ = F*Dᴰ} -×c
          (λ Γᴰ → isFibrationReindex F isFibDᴰ Γᴰ -×c.π₁)
      ∀ⱽF*DᴰPsh = ∀ⱽF*Dᴰ.∀ⱽPsh

      reind-π-weakening-NatIsoᴰ :
        NatIsoᴰ
          (preservesProvidedUniversalElementsNatIso (ProdWithAProf C c)
             (ProdWithAProf D (F-ob F c)) F
             (λ c' → preservesBinProdCones F c' c) -×c -×Fc F-×)
          (π Dᴰ F ∘Fᴰ ∀ⱽF*Dᴰ.weakenπFᴰ)
          (∀ⱽDᴰ.weakenπFᴰ ∘Fᴰ π Dᴰ F)
      reind-π-weakening-NatIsoᴰ .NatIsoᴰ.transᴰ .NatTransᴰ.N-obᴰ xᴰ =
        introᴰ (isFibDᴰ xᴰ -×Fc.π₁) $
          Dᴰ.reind F-×.preserves-π₁ $
            π Dᴰ F .F-homᴰ (Dᴰ.reind (D.⋆IdL _) $ isFibDᴰ xᴰ (F ⟪ -×c.π₁ ⟫) .elementⱽ)
      reind-π-weakening-NatIsoᴰ .NatIsoᴰ.transᴰ .NatTransᴰ.N-homᴰ fᴰ =
        Dᴰ.rectify $ Dᴰ.≡out $
          {!!}
      reind-π-weakening-NatIsoᴰ .NatIsoᴰ.nIsoᴰ = {!!}

      uq-reindex :
        UniversalQuantifier {Cᴰ = F*Dᴰ} {a = c} -×c
          (λ Γᴰ → isFibrationReindex F isFibDᴰ Γᴰ (-×c.π₁))
          dᴰ
      uq-reindex =
          reindUEⱽ ∀dᴰ ◁PshIsoⱽ
          (reindHet∀PshIsoⱽ -×c -×Fc F-×
            (λ Δᴰ → isFibrationReindex F isFibDᴰ Δᴰ -×c.π₁)
            (λ Δᴰ → isFibDᴰ Δᴰ -×Fc.π₁)
            (Dᴰ [-][-, vertexⱽ (isFibDᴰ dᴰ _) ])
            (π Dᴰ F)
            reind-π-weakening-NatIsoᴰ
            ⋆PshIsoⱽ {!!})
          -- asdf -×c -×Fc F-× isFibDᴰ dᴰ
