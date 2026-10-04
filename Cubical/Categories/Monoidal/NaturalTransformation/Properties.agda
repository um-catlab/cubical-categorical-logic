{-# OPTIONS --lossy-unification #-}
{-
  Between product-preserving lax monoidal functors into a cartesian
  monoidal target, every natural transformation is monoidal.

  Setup:
    * source and target use `cartesianMonoidalStr` from
      Cubical.Categories.Monoidal.Cartesian.
    * `IsProductPreserving F` packages what "F preserves products" means
      in this cartesian-monoidal setting: μ_F is iso, μ_F intertwines with
      the projections, and F sends the source unit to a terminal.
-}
module Cubical.Categories.Monoidal.NaturalTransformation.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Categories.Category
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base hiding (MonoidalStr)
open import Cubical.Categories.Monoidal.Cartesian using (cartesianMonoidalStr)
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.Monoidal.NaturalTransformation.Base
open import Cubical.Categories.Limits.Terminal using (Terminal; isTerminal)
open import Cubical.Categories.Limits.BinProduct using (BinProducts; module BinProducts)

open Functor
open NatTrans
open LaxMonoidalFunctor
open isIso

private variable ℓM ℓM' ℓN ℓN' : Level

module _
  {M-Cat : Category ℓM ℓM'} (M-bp : BinProducts M-Cat) (M-term : Terminal M-Cat)
  {N-Cat : Category ℓN ℓN'} (N-bp : BinProducts N-Cat) (N-term : Terminal N-Cat)
  where
  private
    M : MonoidalCategory ℓM ℓM'
    M .MonoidalCategory.C = M-Cat
    M .MonoidalCategory.monstr = cartesianMonoidalStr M-Cat M-bp M-term
    N : MonoidalCategory ℓN ℓN'
    N .MonoidalCategory.C = N-Cat
    N .MonoidalCategory.monstr = cartesianMonoidalStr N-Cat N-bp N-term
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module M-bp = BinProducts M-Cat M-bp
    module N-bp = BinProducts N-Cat N-bp

  record IsProductPreserving (F : LaxMonoidalFunctor M N)
    : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN'))
    where
    private
      module F = LaxMonoidalFunctor F
      Fob = LaxMonoidalFunctor.F F .F-ob
      Fhom : ∀ {x y} → M.C [ x , y ] → N.C [ Fob x , Fob y ]
      Fhom = LaxMonoidalFunctor.F F .F-hom
    field
      μ-isIso  : ∀ x y → isIso N.C (F.μ⟨ x , y ⟩)
      pres-π₁  : ∀ x y →
        F.μ⟨ x , y ⟩ N.⋆ Fhom (M-bp.binProdPr₁ {x}{y}) ≡ N-bp.binProdPr₁ {Fob x}{Fob y}
      pres-π₂  : ∀ x y →
        F.μ⟨ x , y ⟩ N.⋆ Fhom (M-bp.binProdPr₂ {x}{y}) ≡ N-bp.binProdPr₂ {Fob x}{Fob y}
      pres-unit : isTerminal N.C (Fob M.unit)

  module _
    (F G : LaxMonoidalFunctor M N)
    (F-pres : IsProductPreserving F)
    (G-pres : IsProductPreserving G)
    (φ : NatTrans (LaxMonoidalFunctor.F F) (LaxMonoidalFunctor.F G))
    where
    private
      module F = LaxMonoidalFunctor F
      module G = LaxMonoidalFunctor G
      module F-pres = IsProductPreserving F-pres
      module G-pres = IsProductPreserving G-pres

    NatTrans-isMonoidal : MonoidalStr M N F G φ
    NatTrans-isMonoidal .MonoidalStr.ε-law =
      -- G(1_M) is terminal → any two maps into it agree.
      isContr→isProp (G-pres.pres-unit N.unit) _ _
    NatTrans-isMonoidal .MonoidalStr.μ-law x y = μ-law
      where
        Fπ₁ = LaxMonoidalFunctor.F F ⟪ M-bp.binProdPr₁ {x}{y} ⟫
        Fπ₂ = LaxMonoidalFunctor.F F ⟪ M-bp.binProdPr₂ {x}{y} ⟫
        Gπ₁ = LaxMonoidalFunctor.F G ⟪ M-bp.binProdPr₁ {x}{y} ⟫
        Gπ₂ = LaxMonoidalFunctor.F G ⟪ M-bp.binProdPr₂ {x}{y} ⟫
        Fμ  = F.μ⟨ x , y ⟩
        Gμ  = G.μ⟨ x , y ⟩
        Gμ⁻¹     = G-pres.μ-isIso x y .inv
        Gμ⁻¹⋆Gμ  = G-pres.μ-isIso x y .sec
        φφ       = φ ⟦ x ⟧ N.⊗ₕ φ ⟦ y ⟧
        φxy      = φ ⟦ x M.⊗ y ⟧

        -- Kavvos 2020 Thm 5.9, Step 1: naturality of the canonical comparison
        -- map n⁻¹ = ⟨Gπ₁, Gπ₂⟩ w.r.t. φ. Shown by uniqueness of pairing into
        -- Gx ×N Gy: each side projects via N-pr_i to `N-pr_i ⋆ φ_i` (using
        -- G-pres to reduce Gμ⁻¹ ⋆ N-pr_i to Gπ_i, φ naturality at π_i^M,
        -- and F-pres to relate Fμ ⋆ Fπ_i to N-pr_i).
        proj₁-eq : φφ N.⋆ N-bp.binProdPr₁
                 ≡ ((Fμ N.⋆ φxy) N.⋆ Gμ⁻¹) N.⋆ N-bp.binProdPr₁
        proj₁-eq =
            φφ N.⋆ N-bp.binProdPr₁                      ≡⟨ N-bp.binProdArrowPr₁ ⟩
            N-bp.binProdPr₁ N.⋆ φ ⟦ x ⟧                 ≡⟨ cong (N._⋆ _) (sym (F-pres.pres-π₁ x y)) ⟩
            (Fμ N.⋆ Fπ₁) N.⋆ φ ⟦ x ⟧                    ≡⟨ N.⋆Assoc _ _ _ ⟩
            Fμ N.⋆ (Fπ₁ N.⋆ φ ⟦ x ⟧)                    ≡⟨ cong (Fμ N.⋆_) (φ .N-hom _) ⟩
            Fμ N.⋆ (φxy N.⋆ Gπ₁)                        ≡⟨ cong (λ h → Fμ N.⋆ (φxy N.⋆ h)) (sym Gμ⁻¹-π₁) ⟩
            Fμ N.⋆ (φxy N.⋆ (Gμ⁻¹ N.⋆ N-bp.binProdPr₁)) ≡⟨ cong (Fμ N.⋆_) (sym (N.⋆Assoc _ _ _))
                                                                     ∙ sym (N.⋆Assoc _ _ _)
                                                                     ∙ cong (N._⋆ _) (sym (N.⋆Assoc _ _ _)) ⟩
            ((Fμ N.⋆ φxy) N.⋆ Gμ⁻¹) N.⋆ N-bp.binProdPr₁
              ∎
          where
            Gμ⁻¹-π₁ : Gμ⁻¹ N.⋆ N-bp.binProdPr₁ ≡ Gπ₁
            Gμ⁻¹-π₁ = cong (Gμ⁻¹ N.⋆_) (sym (G-pres.pres-π₁ x y))
                    ∙ sym (N.⋆Assoc _ _ _)
                    ∙ cong (N._⋆ Gπ₁) Gμ⁻¹⋆Gμ
                    ∙ N.⋆IdL _

        proj₂-eq : φφ N.⋆ N-bp.binProdPr₂
                 ≡ ((Fμ N.⋆ φxy) N.⋆ Gμ⁻¹) N.⋆ N-bp.binProdPr₂
        proj₂-eq =
            φφ N.⋆ N-bp.binProdPr₂                      ≡⟨ N-bp.binProdArrowPr₂ ⟩
            N-bp.binProdPr₂ N.⋆ φ ⟦ y ⟧                 ≡⟨ cong (N._⋆ _) (sym (F-pres.pres-π₂ x y)) ⟩
            (Fμ N.⋆ Fπ₂) N.⋆ φ ⟦ y ⟧                    ≡⟨ N.⋆Assoc _ _ _ ⟩
            Fμ N.⋆ (Fπ₂ N.⋆ φ ⟦ y ⟧)                    ≡⟨ cong (Fμ N.⋆_) (φ .N-hom _) ⟩
            Fμ N.⋆ (φxy N.⋆ Gπ₂)                        ≡⟨ cong (λ h → Fμ N.⋆ (φxy N.⋆ h)) (sym Gμ⁻¹-π₂) ⟩
            Fμ N.⋆ (φxy N.⋆ (Gμ⁻¹ N.⋆ N-bp.binProdPr₂)) ≡⟨ cong (Fμ N.⋆_) (sym (N.⋆Assoc _ _ _))
                                                                     ∙ sym (N.⋆Assoc _ _ _)
                                                                     ∙ cong (N._⋆ _) (sym (N.⋆Assoc _ _ _)) ⟩
            ((Fμ N.⋆ φxy) N.⋆ Gμ⁻¹) N.⋆ N-bp.binProdPr₂
              ∎
          where
            Gμ⁻¹-π₂ : Gμ⁻¹ N.⋆ N-bp.binProdPr₂ ≡ Gπ₂
            Gμ⁻¹-π₂ = cong (Gμ⁻¹ N.⋆_) (sym (G-pres.pres-π₂ x y))
                    ∙ sym (N.⋆Assoc _ _ _)
                    ∙ cong (N._⋆ Gπ₂) Gμ⁻¹⋆Gμ
                    ∙ N.⋆IdL _

        -- Kavvos 5.9's fused Steps 1+2: uniqueness of pairing to identify
        -- φφ with (Fμ ⋆ φxy) ⋆ Gμ⁻¹, then post-compose Gμ ("invert n") to
        -- yield the μ-law.
        μ-law : φφ N.⋆ Gμ ≡ Fμ N.⋆ φxy
        μ-law =
            φφ N.⋆ Gμ
              ≡⟨ cong (N._⋆ Gμ) φφ≡RHS⋆Gμ⁻¹ ⟩
            ((Fμ N.⋆ φxy) N.⋆ Gμ⁻¹) N.⋆ Gμ
              ≡⟨ N.⋆Assoc _ _ _
               ∙ cong ((Fμ N.⋆ φxy) N.⋆_) Gμ⁻¹⋆Gμ
               ∙ N.⋆IdR _ ⟩
            Fμ N.⋆ φxy
              ∎
          where
            φφ≡RHS⋆Gμ⁻¹ : φφ ≡ (Fμ N.⋆ φxy) N.⋆ Gμ⁻¹
            φφ≡RHS⋆Gμ⁻¹ =
                sym (N-bp.binProdArrowUnique {h = φφ} refl refl)
              ∙ N-bp.binProdArrowUnique (sym proj₁-eq) (sym proj₂-eq)
