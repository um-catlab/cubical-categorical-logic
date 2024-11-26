{-
  Reindexing a displayed cartesian category along a cartesian functor inherits a
  displayed cartesian category structure if we have cartesian lifts
-}
{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Constructions.Reindex.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Cartesian.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Functor
open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
import      Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Fibration.IsoFibration
open import Cubical.Categories.Displayed.HLevels
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS : Level

module _
  {C : CartesianCategory ℓC ℓC'}
  {D : CartesianCategory ℓD ℓD'}
  (Dᴰ : CartesianCategoryᴰ D ℓDᴰ ℓDᴰ')
  (F : CartesianFunctor (C .fst) (D .fst))
  where
  open CartesianFunctor
  open UniversalElement
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
      𝟙-iso : CatIso _ D-𝟙'.𝟙 D.𝟙
      𝟙-iso = terminalToIso _ TerminalD' (D .snd .fst)
      𝟙-isoLift : WeakIsoLift _ _ _
      𝟙-isoLift = isoLift Dᴰ.𝟙ᴰ 𝟙-iso
      module _ {c c' : C.ob} where
        BinProductsD' : UniversalElement _ (BinProductProf (D .fst) ⟅ F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆ ⟆)
        BinProductsD' .vertex = _
        BinProductsD' .element = _
        BinProductsD' .universal = F .PreservesBinProducts _ _ (C.CCBinProducts'' c c')
        BinProductsD : UniversalElement _ (BinProductProf (D .fst) ⟅ F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆ ⟆)
        BinProductsD = BinProductToRepresentable _ (D .snd .snd _ _)
        BinProductsD'' : BinProduct' _ (F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆)
        BinProductsD'' = RepresentableToBinProduct' _ BinProductsD'
        module D-×' = BinProduct'Notation BinProductsD''
        module D-× = BinProduct'Notation (D.CCBinProducts' (F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆))
        ×-iso : CatIso (D .fst) D-×'.vert D-×.vert
        ×-iso = UniversalElements→Iso BinProductsD'' (D.CCBinProducts' (F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆))
        -- how do I move this up here without too many module hassles
        --×-isoLift : WeakIsoLift _ _ _
        --×-isoLift = isoLift ({!!} Dᴰ.×ᴰ {!!}) {!!}
        foo = UniversalElements→CanonicalIso BinProductsD'' (D.CCBinProducts' (F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆))
    open Functor
    reindex : CartesianCategoryᴰ C ℓDᴰ ℓDᴰ'
    reindex .fst = Reindex.reindex (Dᴰ .fst) (F .|F|)
    reindex .snd .fst .vertexᴰ = 𝟙-isoLift .f*cᴰ
    reindex .snd .fst .elementᴰ = _
    reindex .snd .fst .universalᴰ {xᴰ = xᴰ} .equiv-proof _ = uniqueExists
      (R.reind D-𝟙'.𝟙η' (Dᴰ.!tᴰ _ Dᴰ.⋆ᴰ 𝟙-isoLift .σ))
      refl
      (λ _ _ _ → refl)
      (λ _ _ → hasPropHoms _ _ _ _ _)
    reindex .snd .snd (Fcᴰ , Fc'ᴰ) .vertexᴰ = isoLift (Fcᴰ Dᴰ.×ᴰ Fc'ᴰ) ×-iso .f*cᴰ
    reindex .snd .snd (Fcᴰ , Fc'ᴰ) .elementᴰ .fst = R.reind (cong fst foo) (isoLift (Fcᴰ Dᴰ.×ᴰ Fc'ᴰ) ×-iso .π Dᴰ.⋆ᴰ Dᴰ.π₁ᴰ)
    reindex .snd .snd (Fcᴰ , Fc'ᴰ) .elementᴰ .snd = R.reind (cong snd foo) (isoLift (Fcᴰ Dᴰ.×ᴰ Fc'ᴰ) ×-iso .π Dᴰ.⋆ᴰ Dᴰ.π₂ᴰ)
    reindex .snd .snd {d = c , c'} (Fcᴰ , Fc'ᴰ) .universalᴰ {f = f} .equiv-proof (a , b) = uniqueExists
      (R.reind
        (UniversalElements-triangle' BinProductsD'' (D.CCBinProducts' (F .|F| ⟅ c ⟆ , F .|F| ⟅ c' ⟆)) _ ∙
          cong₂ D-×'._,p_ (F .|F| .F-seq _ _) (F .|F| .F-seq _ _) ∙
          sym D-×'.×η)
        (a Dᴰ.,pᴰ b Dᴰ.⋆ᴰ isoLift (Fcᴰ Dᴰ.×ᴰ Fc'ᴰ) ×-iso .σ))
      (ΣPathP (hasPropHoms _ _ _ _ _ , hasPropHoms _ _ _ _ _))
      (λ _ _ _ → isProp→isSet (isPropΣ (hasPropHoms _ _ _) (λ _ → hasPropHoms _ _ _)) _ _ _ _)
      (λ _ _ → hasPropHoms _ _ _ _ _)
