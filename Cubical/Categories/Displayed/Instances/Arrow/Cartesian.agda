{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Arrow.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import Cubical.Categories.Limits.Cartesian.Base
import Cubical.Categories.Displayed.Instances.Arrow.Base as Arrow
import Cubical.Categories.Displayed.Instances.Arrow.Properties as Arrow
open import Cubical.Categories.Limits.Cartesian.Functor
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.Cartesian
open import Cubical.Categories.Constructions.BinProduct.Redundant hiding (_×C_)

open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Constructions.Reindex.Cartesian

open UniversalElement
open UniversalElementᴰ

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category
open Functor

module _ (C : CartesianCategory ℓC ℓC') where
  open isIso
  private
    module C = CartesianCategoryNotation C
    hasPropHomsIso = Arrow.hasPropHomsIso (C .fst)

  Iso : CartesianCategoryᴰ (C ×C C) ℓC' ℓC'
  Iso .fst = Arrow.Iso (C .fst)
  Iso .snd .fst .vertexᴰ = idCatIso
  Iso .snd .fst .elementᴰ = tt
  Iso .snd .fst .universalᴰ {xᴰ = xᴰ} .equiv-proof _ = uniqueExists
    (C.𝟙η' , _)
    refl
    (λ _ _ _ → refl)
    λ _ _ → hasPropHomsIso _ xᴰ idCatIso _ _
  Iso .snd .snd ((f , p) , (g , q)) .vertexᴰ = preserveIsosF
    -- this is probably unnecessary, but I don't see a lemma about bifunctors preserving catisos
    {F = C.×pF ∘F (ProdToRedundant _ _)}
    ((f , g) , isiso (p .inv , q .inv) (≡-× (p .sec) (q .sec)) (≡-× (p .ret) (q .ret)))
  Iso .snd .snd {d = (c , c') , (c'' , c''')} ((f , p) , (g , q)) .elementᴰ = (sym C.×β₁ , _) , (sym C.×β₂ , _)
  Iso .snd .snd {d = (c , c') , (c'' , c''')} ((f , p) , (g , q)) .universalᴰ {x = (cₓ , c'ₓ)} {xᴰ = (fₓ , pₓ)} {f = h , h'} .equiv-proof ((r , _) , (s , _)) =
    uniqueExists
    (C.×-extensionality
      (C.⋆Assoc _ _ _ ∙ congS (h C.⋆_) C.×β₁ ∙ sym (C.⋆Assoc _ _ _) ∙ r ∙ sym (C.⋆Assoc _ _ _))
      (C.⋆Assoc _ _ _ ∙ congS (h C.⋆_) C.×β₂ ∙ sym (C.⋆Assoc _ _ _) ∙ s ∙ sym (C.⋆Assoc _ _ _)) , _)
    (≡-× (hasPropHomsIso _ _ _ _ _) (hasPropHomsIso _ _ _ _ _))
    (λ _ _ _ → isProp→isSet (isProp× (hasPropHomsIso _ _ _) (hasPropHomsIso _ _ _)) _ _ _ _)
    (λ _ _ → ≡-× (C.isSetHom _ _ _ _) refl)

module _ {C : CartesianCategory ℓC ℓC'} {D : CartesianCategory ℓD ℓD'}
  (F G : CartesianFunctor (C .fst) (D .fst))
  where
  IsoComma : CartesianCategoryᴰ C _ _
  IsoComma = reindex (Iso D) (_,F_ {A = C} F G) (Arrow.hasPropHomsIso _) (Arrow.isIsoFibrationIso _)
