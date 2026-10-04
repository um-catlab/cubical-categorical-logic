-- SET as a cartesian monoidal category, packaged via
-- `CartesianMonoidalCategory` so its `.asMonoidal` view is the standard
-- cartesian monoidal structure on sets.
module Cubical.Categories.Monoidal.Instances.Sets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.Terminal using (Terminal)
open import Cubical.Categories.Limits.BinProduct using (BinProducts; BinProduct)
open import Cubical.Categories.Monoidal
open import Cubical.Categories.Monoidal.Cartesian.More
  using (CartesianMonoidalCategory)

private variable ℓ : Level

SET-term : Terminal (SET ℓ)
SET-term .fst = Unit* , isSetUnit*
SET-term .snd Y = (λ _ → tt*) , λ ! → funExt λ _ → refl

SET-bp : BinProducts (SET ℓ)
SET-bp X Y .BinProduct.binProdOb  = X .fst × Y .fst , isSet× (X .snd) (Y .snd)
SET-bp X Y .BinProduct.binProdPr₁ = fst
SET-bp X Y .BinProduct.binProdPr₂ = snd
SET-bp X Y .BinProduct.univProp f g =
  ((λ z → f z , g z) , refl , refl) ,
  λ (h , h⋆π₁≡f , h⋆π₂≡g) →
    Σ≡Prop (λ _ → isProp× (isSet→ (X .snd) _ _) (isSet→ (Y .snd) _ _))
      (funExt λ z i → h⋆π₁≡f (~ i) z , h⋆π₂≡g (~ i) z)

SETCartMon : CartesianMonoidalCategory (ℓ-suc ℓ) ℓ
SETCartMon .CartesianMonoidalCategory.C    = SET _
SETCartMon .CartesianMonoidalCategory.bp   = SET-bp
SETCartMon .CartesianMonoidalCategory.term = SET-term

open CartesianMonoidalCategory

SETMon : MonoidalCategory (ℓ-suc ℓ) ℓ
SETMon = asMonoidal SETCartMon 
