module Cubical.Categories.LocallySmall.Instances.Level where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Functor
open import Cubical.Categories.LocallySmall.Bifunctor.Base
open import Cubical.Categories.LocallySmall.Constructions.BinProduct
open import Cubical.Categories.LocallySmall.Instances.Indiscrete

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
