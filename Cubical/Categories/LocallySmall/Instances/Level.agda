module Cubical.Categories.LocallySmall.Instances.Level where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Constructions.ChangeOfObjects
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.HomPropertyOver

LEVEL  : GloballySmallCategory (Liftω Level) ℓ-zero
LEVEL  = Indiscrete (Liftω Level)

open Functor
open Bifunctor

ℓ-MAXBif : Bifunctor LEVEL LEVEL LEVEL
ℓ-MAXBif .Bif-ob (liftω ℓ) (liftω ℓ') = liftω (ℓ-max ℓ ℓ')
ℓ-MAXBif .Bif-hom× _ _ = _
ℓ-MAXBif .Bif-homL _ _ = _
ℓ-MAXBif .Bif-homR _ _ = _
ℓ-MAXBif .Bif-×-id = refl
ℓ-MAXBif .Bif-×-seq = refl
ℓ-MAXBif .Bif-L×-agree _ _ = refl
ℓ-MAXBif .Bif-R×-agree _ _  = refl

ℓ-MAX : Functor (LEVEL ×C LEVEL) LEVEL
ℓ-MAX = BifunctorToParFunctor ℓ-MAXBif

_Level≤_ : Level → Level → Type
ℓ Level≤ ℓ' = PT.∥ ℓ-max ℓ ℓ' ≡ ℓ' ∥₁

open HomPropertyOver
Level≤HomProperty : HomPropertyOver LEVEL ℓ-zero
Level≤HomProperty .Hom[_][-,-] {x = liftω ℓ} {y = liftω ℓ'} _ = ℓ Level≤ ℓ'
Level≤HomProperty .isPropHomᴰ _ = isPropPropTrunc
Level≤HomProperty .idᴰ = ∣ refl ∣₁
Level≤HomProperty ._⋆ᴰ_ {x = liftω ℓ} {y = liftω ℓ'} {z = liftω ℓ''} _ _
  ∣ℓ≤ℓ'∣ ∣ℓ'≤ℓ''∣ =
  PT.rec2 isPropPropTrunc
    (λ ℓ≤ℓ' ℓ'≤ℓ'' →
      ∣ cong (ℓ-max ℓ) (sym ℓ'≤ℓ'')
      ∙ cong (ℓ-max ℓ'') ℓ≤ℓ'
      ∙ ℓ'≤ℓ'' ∣₁)
    ∣ℓ≤ℓ'∣ ∣ℓ'≤ℓ''∣

open Categoryᴰ
LIFTABLE-LEVEL' : Category (Σω[ ℓ ∈ Liftω Level ] _) _
LIFTABLE-LEVEL' = ∫C (HomPropertyOver→Catᴰ Level≤HomProperty)

LIFTABLE-LEVEL : Category (Liftω Level) _
LIFTABLE-LEVEL =
  ChangeOfObjects {X = Liftω Level} LIFTABLE-LEVEL'
    λ (liftω ℓ) → (liftω ℓ) , (liftω _)

LIFTABLE-LEVEL-π : Functor LIFTABLE-LEVEL LEVEL
LIFTABLE-LEVEL-π .F-ob ℓ = ℓ
LIFTABLE-LEVEL-π .F-hom f = f .fst
LIFTABLE-LEVEL-π .F-id = refl
LIFTABLE-LEVEL-π .F-seq = λ _ _ → refl
