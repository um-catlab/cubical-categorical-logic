module Cubical.Categories.LocallySmall.Displayed.Instances.Sets.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Instances.Level

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base

open Category
open Categoryᴰ
open Σω

SET : SmallFibersCategoryᴰ LEVEL _ (λ (liftω ℓ) → hSet ℓ) _
SET .Hom[_][_,_] _ (liftω X) (liftω Y) = ⟨ X ⟩ → ⟨ Y ⟩
SET .idᴰ = λ z → z
SET ._⋆ᴰ_ = λ g f x → f (g x)
SET .⋆IdLᴰ = λ _ → refl
SET .⋆IdRᴰ = λ _ → refl
SET .⋆Assocᴰ = λ _ _ _ → refl
SET .isSetHomᴰ {yᴰ = (liftω Y)} = isSet→ (Y .snd)

⟨_⟩Set : ∀ {ℓ} → hSet ℓ → Category.Ob (∫C SET)
⟨ A ⟩Set = mk∫Ob SET (liftω A)

open Bifunctorᴰ
×SETBif : Bifunctorᴰ ℓ-MAXBif SET SET SET
×SETBif .Bif-obᴰ (liftω A) (liftω B) =
  liftω (⟨ A ⟩ × ⟨ B ⟩ , isSet× (A .snd) (B .snd))
×SETBif .Bif-hom×ᴰ = λ fᴰ gᴰ z → fᴰ (z .fst) , gᴰ (z .snd)
×SETBif .Bif-homLᴰ = λ fᴰ dᴰ z → fᴰ (z .fst) , z .snd
×SETBif .Bif-homRᴰ = λ cᴰ gᴰ z → z .fst , gᴰ (z .snd)
×SETBif .Bif-×-idᴰ = refl
×SETBif .Bif-×-seqᴰ = refl
×SETBif .Bif-L×-agreeᴰ _ _ = refl
×SETBif .Bif-R×-agreeᴰ _ _ = refl

×SET : Functorᴰ ℓ-MAX (SET ×CᴰSF SET) SET
×SET = BifunctorᴰToParFunctorᴰSF ×SETBif
