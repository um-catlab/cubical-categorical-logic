module Cubical.Categories.Displayed.Instances.CoEilenbergMoore.Comparison where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.Coalgebras
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Displayed.Instances.CoEilenbergMoore
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
    W = L ∘F R
    module W = Functor W

    εW : ∀ x → D [ Functor.F-ob W x , x ]
    εW x = ε ⟦ x ⟧
    δW : ∀ x → D [ Functor.F-ob W x , Functor.F-ob W (Functor.F-ob W x) ]
    δW x = L ⟪ η ⟦ R ⟅ x ⟆ ⟧ ⟫

  CoalgebraSection : Section (L ^opF) (CoAlgCatᴰ W)
  CoalgebraSection = mkPropHomsSection
    (hasPropHomsStructureOver (AlgStructureOver (W ^opF)))
    (λ c → L ⟪ η ⟦ c ⟧ ⟫)
    (λ {c}{c'} f →
      sym (L.F-seq _ _)
      ∙ cong (L ⟪_⟫) (η .N-hom f)
      ∙ L.F-seq _ _)

  CoalgComparison : Functor (C ^op) (∫C (CoAlgCatᴰ W))
  CoalgComparison = intro (L ^opF) CoalgebraSection

  CoEMSection : Section CoalgComparison (coEMCatᴰ W εW δW)
  CoEMSection = mkPropHomsSection
    (hasPropHomsStructureOver (coEMStructureOver W εW δW))
    (λ c → Δ₁ c
         , ( sym (L.F-seq _ _)
           ∙ cong (L ⟪_⟫) (η .N-hom (η ⟦ c ⟧))
           ∙ L.F-seq _ _ ))
    (λ _ → tt)

  ComparisonCoEM : Functor C (coEMCategory W εW δW)
  ComparisonCoEM = (intro CoalgComparison CoEMSection ^opF) ∘F toOpOp
