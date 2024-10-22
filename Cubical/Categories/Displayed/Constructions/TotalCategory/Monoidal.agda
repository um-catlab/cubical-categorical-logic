{-

  If M and N are monoidal categories, then weaken M.C N.C can be given
  the structure of a displayed monoidal category.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.TotalCategory.Monoidal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Constructions.BinProduct.Monoidal

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalIsomorphism
open import Cubical.Categories.Displayed.Monoidal.Base
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct
import Cubical.Categories.Displayed.Reasoning as Reasoning
import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
  as TotalCatᴰ

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _ (M : MonoidalCategory ℓC ℓC')
         (N : MonoidalCategory ℓD ℓD')
         (P : MonoidalCategoryᴰ (M ×M N) ℓE ℓE')
         where
  open Category
  open MonoidalCategoryᴰ
  open TensorStrᴰ
  open MonoidalStrᴰ
  open Functorᴰ
  open Functor
  open NatTransᴰ
  open NatIsoᴰ
  open isIsoᴰ
  open NatTrans
  open NatIso
  open isIso
  private
    module M = MonoidalCategory M
    module N = MonoidalCategory N
    module P = MonoidalCategoryᴰ P
    module PR = Reasoning P.Cᴰ

  ∫Mᴰsr : MonoidalCategoryᴰ M (ℓ-max ℓD ℓE) (ℓ-max ℓD' ℓE')
  ∫Mᴰsr .Cᴰ = TotalCatᴰ.∫Cᴰsr {C = M.C}{D = N.C} P.Cᴰ
  -- TODO: maybe could have used an intro principle for ∫Cᴰsr here
  -- TODO: maybe all of this could be from intro principles for ∫Cᴰ?
  ∫Mᴰsr .monstrᴰ .tenstrᴰ .─⊗ᴰ─ .F-obᴰ {m , m'}
    ((n , p) , (n' , p')) = (n N.⊗ n') , (p P.⊗ᴰ p')
  ∫Mᴰsr .monstrᴰ .tenstrᴰ .─⊗ᴰ─ .F-homᴰ
    ((f , fᴰ) , (g , gᴰ)) = (f N.⊗ₕ g) , (fᴰ P.⊗ₕᴰ gᴰ)
  ∫Mᴰsr .monstrᴰ .tenstrᴰ .─⊗ᴰ─ .F-idᴰ =
    ΣPathP ((N.─⊗─ .F-id) , PR.rectify (P.─⊗ᴰ─ .F-idᴰ))
  ∫Mᴰsr .monstrᴰ .tenstrᴰ .─⊗ᴰ─ .F-seqᴰ fᴰ gᴰ =
    ΣPathP ((N.─⊗─ .F-seq _ _) , PR.rectify (P.─⊗ᴰ─ .F-seqᴰ _ _))
  ∫Mᴰsr .monstrᴰ .tenstrᴰ .unitᴰ = N.unit , P.unitᴰ
  ∫Mᴰsr .monstrᴰ .αᴰ .transᴰ .N-obᴰ xᴰ =
    N.α⟨ _ , _ , _ ⟩ , P.αᴰ⟨ _ , _ , _ ⟩
  ∫Mᴰsr .monstrᴰ .αᴰ .transᴰ .N-homᴰ fᴰ = ΣPathP
    (N.α .trans .N-hom _ , P.αᴰ .transᴰ .N-homᴰ _)
  ∫Mᴰsr .monstrᴰ .αᴰ .nIsoᴰ xᴰ .invᴰ =
    N.α⁻¹⟨ _ , _ , _ ⟩ , P.α⁻¹ᴰ⟨ _ , _ , _ ⟩
  ∫Mᴰsr .monstrᴰ .αᴰ .nIsoᴰ xᴰ .secᴰ =
    ΣPathP ((N.α .nIso _ .sec) , (P.αᴰ .nIsoᴰ _ .secᴰ))
  ∫Mᴰsr .monstrᴰ .αᴰ .nIsoᴰ xᴰ .retᴰ =
    ΣPathP ((N.α .nIso _ .ret) , (P.αᴰ .nIsoᴰ _ .retᴰ))
  ∫Mᴰsr .monstrᴰ .ηᴰ .transᴰ .N-obᴰ _ = N.η⟨ _ ⟩ , P.ηᴰ⟨ _ ⟩
  ∫Mᴰsr .monstrᴰ .ηᴰ .transᴰ .N-homᴰ _ =
    ΣPathP (N.η .trans .N-hom _ , P.ηᴰ .transᴰ .N-homᴰ _)
  ∫Mᴰsr .monstrᴰ .ηᴰ .nIsoᴰ xᴰ .invᴰ = N.η⁻¹⟨ _ ⟩ , P.η⁻¹ᴰ⟨ _ ⟩
  ∫Mᴰsr .monstrᴰ .ηᴰ .nIsoᴰ xᴰ .secᴰ =
    ΣPathP ((N.η .nIso _ .sec) , (P.ηᴰ .nIsoᴰ _ .secᴰ))
  ∫Mᴰsr .monstrᴰ .ηᴰ .nIsoᴰ xᴰ .retᴰ =
    ΣPathP ((N.η .nIso _ .ret) , (P.ηᴰ .nIsoᴰ _ .retᴰ))
  ∫Mᴰsr .monstrᴰ .ρᴰ .transᴰ .N-obᴰ _ = N.ρ⟨ _ ⟩ , P.ρᴰ⟨ _ ⟩
  ∫Mᴰsr .monstrᴰ .ρᴰ .transᴰ .N-homᴰ _ =
    ΣPathP (N.ρ .trans .N-hom _ , P.ρᴰ .transᴰ .N-homᴰ _)
  ∫Mᴰsr .monstrᴰ .ρᴰ .nIsoᴰ xᴰ .invᴰ = N.ρ⁻¹⟨ _ ⟩ , P.ρ⁻¹ᴰ⟨ _ ⟩
  ∫Mᴰsr .monstrᴰ .ρᴰ .nIsoᴰ xᴰ .secᴰ =
    ΣPathP ((N.ρ .nIso _ .sec) , (P.ρᴰ .nIsoᴰ _ .secᴰ))
  ∫Mᴰsr .monstrᴰ .ρᴰ .nIsoᴰ xᴰ .retᴰ =
    ΣPathP ((N.ρ .nIso _ .ret) , (P.ρᴰ .nIsoᴰ _ .retᴰ))
  ∫Mᴰsr .monstrᴰ .pentagonᴰ wᴰ xᴰ yᴰ zᴰ =
    ΣPathP (N.pentagon _ _ _ _ , P.pentagonᴰ _ _ _ _)
  ∫Mᴰsr .monstrᴰ .triangleᴰ _ _ = ΣPathP (N.triangle _ _ , P.triangleᴰ _ _)
