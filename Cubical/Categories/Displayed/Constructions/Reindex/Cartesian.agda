{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Functor
open import Cubical.Categories.Category

open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Fibration.IsoFibration
open import Cubical.Categories.Displayed.HLevels
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _
  {C : CartesianCategory ℓC ℓC'}
  {D : CartesianCategory ℓD ℓD'}
  (Dᴰ : CartesianCategoryᴰ D ℓDᴰ ℓDᴰ')
  (F : CartesianFunctor (C .fst) (D .fst))
  where
  open CartesianFunctor
  open UniversalElementᴰ
  private
    module C = CartesianCategoryNotation C
    module D = CartesianCategoryNotation D
    module Dᴰ = CartesianCategoryᴰNotation Dᴰ
    module R = HomᴰReasoning (Dᴰ .fst)
  module _
    (hasPropHoms : hasPropHoms (Dᴰ .fst))
    (isoLift : isWeakIsoFibration (Dᴰ .fst))
    where
    open WeakIsoLift
    open isIso
    private
      TerminalD' : Terminal (D .fst)
      TerminalD' = F .|F| ⟅ C.𝟙 ⟆ , F .PreservesTerminal (C .snd .fst)
      module D-𝟙' = TerminalNotation _ TerminalD'
      module _ (c c' : C.ob) where
        BinProductsD' : {!!}
        BinProductsD' = {!F .PreservesBinProducts _ _ (C.CCBinProducts'' c c') !}
    𝟙-iso : CatIso _ D-𝟙'.𝟙 D.𝟙
    𝟙-iso = terminalToIso _ TerminalD' (D .snd .fst)
    reindex : CartesianCategoryᴰ C ℓDᴰ ℓDᴰ'
    reindex .fst = Reindex.reindex (Dᴰ .fst) (F .|F|)
    reindex .snd .fst .vertexᴰ = isoLift Dᴰ.𝟙ᴰ 𝟙-iso .f*cᴰ
    reindex .snd .fst .elementᴰ = _
    reindex .snd .fst .universalᴰ {xᴰ = xᴰ} .equiv-proof _ = uniqueExists
      (R.reind D-𝟙'.𝟙η' (Dᴰ.!tᴰ _ Dᴰ.⋆ᴰ isoLift Dᴰ.𝟙ᴰ 𝟙-iso .σ))
      refl
      (λ _ _ _ → refl)
      (λ _ _ → hasPropHoms _ _ _ _ _)
    reindex .snd .snd = {!!}
