-- The Eilenberg–Moore comparison functor of an adjunction L ⊣ R.
module Cubical.Categories.Displayed.Instances.EilenbergMoore.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Adjoint.Monad
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras
open import Cubical.Categories.Displayed.Instances.PropertyOver
  using (hasContrHomsPropertyOver)
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
    module R = Functor R
    T = R ∘F L

    Mon : Monad C
    Mon = T , MonadFromAdjunction L R adj

  AlgebraSection : Section R (ALGᴰ T)
  AlgebraSection = mkPropHomsSection
    (hasPropHomsStructureOver (AlgStructureOver T))
    (λ d → R ⟪ ε ⟦ d ⟧ ⟫)
    (λ {d}{d'} f →
      sym (R.F-seq _ _)
      ∙ cong (R ⟪_⟫) (sym (ε .N-hom f))
      ∙ R.F-seq _ _)

  ComparisonAlg : Functor D (∫C (ALGᴰ T))
  ComparisonAlg = intro R AlgebraSection

  EMSection : Section ComparisonAlg (EMᴰ Mon)
  EMSection = mkContrHomsSection
    (hasContrHomsPropertyOver (∫C (ALGᴰ T)) (isEMAlgebra Mon))
    (λ d → Δ₂ d
         , ( sym (R.F-seq _ _)
           ∙ cong (R ⟪_⟫) (sym (ε .N-hom (ε ⟦ d ⟧)))
           ∙ R.F-seq _ _ ))

  ComparisonEM : Functor D (EM Mon)
  ComparisonEM = intro ComparisonAlg EMSection
