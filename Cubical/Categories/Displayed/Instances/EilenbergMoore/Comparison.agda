-- The Eilenberg–Moore comparison functor of an adjunction L ⊣ R.
module Cubical.Categories.Displayed.Instances.EilenbergMoore.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Instances.EilenbergMoore
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.TotalCategory.Properties

private
  variable ℓC ℓC' ℓD ℓD' : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (L : Functor C D) (R : Functor D C) (adj : UnitCounit._⊣_ L R) where

  open UnitCounit
  open _⊣_ adj
  open NatTrans

  private
    module C = Category C
    module D = Category D
    module L = Functor L
    module R = Functor R
    T = R ∘F L
    module T = Functor T

    Mon : Monad C
    Mon = T , MonadFromAdjunction L R adj

  AlgebraSection : Section R (AlgCatᴰ T)
  AlgebraSection = mkPropHomsSection
    (hasPropHomsStructureOver (AlgStructureOver T))
    (λ d → R ⟪ ε ⟦ d ⟧ ⟫)
    (λ {d}{d'} f →
      sym (R.F-seq _ _)
      ∙ cong (R ⟪_⟫) (sym (ε .N-hom f))
      ∙ R.F-seq _ _)

  ComparisonAlg : Functor D (∫C (AlgCatᴰ T))
  ComparisonAlg = intro R AlgebraSection

  EMSection : Section ComparisonAlg (EMCatᴰ Mon)
  EMSection = mkPropHomsSection
    (hasPropHomsStructureOver (EMStructureOver Mon))
    (λ d → Δ₂ d
         , ( sym (R.F-seq _ _)
           ∙ cong (R ⟪_⟫) (sym (ε .N-hom (ε ⟦ d ⟧)))
           ∙ R.F-seq _ _ ))
    (λ _ → tt)

  ComparisonEM : Functor D (EMCategory Mon)
  ComparisonEM = intro ComparisonAlg EMSection
