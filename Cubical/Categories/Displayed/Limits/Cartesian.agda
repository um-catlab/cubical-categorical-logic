{-# OPTIONS --safe #-}
-- Note: Max wrote this at first
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Adjoint.More
open import Cubical.Categories.Displayed.Constructions.Slice
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct
open import Agda.Builtin.Cubical.Equiv
open import Cubical.Categories.Presheaf.Representable

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

CartesianCategoryᴰ : CartesianCategory ℓC ℓC' → (ℓ ℓ' : Level) → Type _
CartesianCategoryᴰ CC ℓ ℓ' =
  Σ[ Cᴰ ∈ Categoryᴰ (CC .fst) ℓ ℓ' ]
  {!!} × BinProductsᴰ Cᴰ bps
  where
  bps : BinProducts' (CC .fst)
  bps d = record { vertex = foo .BinProduct.binProdOb

                 ; element = foo .BinProduct.binProdPr₁ , foo .BinProduct.binProdPr₂
                 ; universal = λ A → record { equiv-proof = λ y → ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .fst) , ΣPathP ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .snd .fst) , ((foo .BinProduct.univProp (y .fst) (y .snd) .fst .snd .snd)))) , λ y₁ → {!!} } }
    where
    foo = CC .snd .snd (d .fst) (d .snd)
  -- Terminalᴰ Cᴰ (CC .snd .fst) × BinProductsᴰ Cᴰ (CC .snd .snd)

module _ (C : Category ℓC ℓC')(∃!prod : BinProducts C) where
  lemma : BinProducts' C
  lemma (Γ , Δ) = record
    { vertex = ∃!prod Γ Δ .BinProduct.binProdOb
    ; element = ∃!prod Γ Δ .BinProduct.binProdPr₁ , ∃!prod Γ Δ .BinProduct.binProdPr₂
    ; universal = {!!}
    --λ θ → record { equiv-proof = λ (δ , δ') → {!!} }
    }

  --lemaaa : ?
  --lemaaa = ∃!prod Γ Δ .BinProduct.univProp δ δ'

  lemmaa : (Γ Δ θ : C .Category.ob) →
    isEquiv (λ (f : C [ θ , ∃!prod Γ Δ .BinProduct.binProdOb ]) → (f ⋆⟨ C ⟩ ∃!prod Γ Δ .BinProduct.binProdPr₁ , f ⋆⟨ C ⟩ ∃!prod Γ Δ .BinProduct.binProdPr₂))
  equiv-proof (lemmaa Γ Δ θ) (δ , δ') = (∃!prod Γ Δ .BinProduct.univProp δ δ' .fst .fst , {!!}) , {!!}

  lemma' : BinProducts' C
  lemma' (Γ , Δ) .UniversalElement.vertex = ∃!prod Γ Δ .BinProduct.binProdOb
  lemma' (Γ , Δ) .UniversalElement.element = ∃!prod Γ Δ .BinProduct.binProdPr₁ , ∃!prod Γ Δ .BinProduct.binProdPr₂
  lemma' (Γ , Δ) .UniversalElement.universal θ = lemmaa Γ Δ θ
