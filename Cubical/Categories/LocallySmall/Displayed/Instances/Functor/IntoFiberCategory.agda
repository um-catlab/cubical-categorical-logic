
module Cubical.Categories.LocallySmall.Displayed.Instances.Functor.IntoFiberCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.Functor.IntoFiberCategory
import Cubical.Categories.LocallySmall.Functor as LocallySmallF
open import Cubical.Categories.LocallySmall.NaturalTransformation.IntoFiberCategory
open import Cubical.Categories.LocallySmall.Instances.Indiscrete
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Constructions.ChangeOfObjects

open import Cubical.Categories.LocallySmall.Displayed.Category
import Cubical.Categories.LocallySmall.Displayed.Functor.Base as LocallySmallFᴰ
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Weaken
open import Cubical.Categories.LocallySmall.Displayed.Constructions.ChangeOfObjects
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties
open import Cubical.Categories.LocallySmall.Displayed.Constructions.BinProduct.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Base
open import Cubical.Categories.LocallySmall.Displayed.NaturalTransformation.IntoFiberCategory.Eq

open Category
open Categoryᴰ

open LocallySmallF.Functor
open LocallySmallFᴰ.Functorᴰ
open Liftω
open Σω

module _
  {C : SmallCategory ℓC ℓC'}
  {ℓCᴰ ℓCᴰ'}
  (Cᴰ : SmallCategoryᴰ C ℓCᴰ ℓCᴰ')
  {D : Category Dob DHom-ℓ}
  {Dobᴰ DHom-ℓᴰ}
  (Dᴰ : GloballySmallCategoryᴰ D Dobᴰ DHom-ℓᴰ)
  {Eob-ℓᴰ Eobᴰ EHom-ℓᴰ}
  (Eᴰ : SmallFibersCategoryᴰ D Eob-ℓᴰ Eobᴰ EHom-ℓᴰ)
  {Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ}
  (Dᴰᴰ : SmallFibersᴰCategoryᴰ Dᴰ Eᴰ Dᴰᴰ-ℓ Dobᴰᴰ DHom-ℓᴰᴰ)
  where
  open NatTransᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ
  open FunctorEqᴰDefs Cᴰ Dᴰ Eᴰ Dᴰᴰ
  open NatTransᴰ
  private
    module C = SmallCategory C
    module Cᴰ = SmallCategoryᴰ Cᴰ
    module D = CategoryNotation D
    module Dᴰ = CategoryᴰNotation Dᴰ
    module Eᴰ = CategoryᴰNotation Eᴰ
    module Dᴰᴰ = CategoryᴰNotation Dᴰᴰ

    C⇒Eᴰ : Categoryᴰ D Functor _
    C⇒Eᴰ = FUNCTOR C Eᴰ

    Dᴰ×C⇒Eᴰ = Dᴰ ×ᴰ C⇒Eᴰ
    Dᴰ×Eᴰ = Dᴰ ×ᴰ Eᴰ
    module Dᴰ×C⇒Eᴰ = CategoryᴰNotation Dᴰ×C⇒Eᴰ
    module Dᴰ×Eᴰ = CategoryᴰNotation Dᴰ×Eᴰ

  FUNCTORᴰ :
    Categoryᴰ Dᴰ×C⇒Eᴰ.∫C (λ (d , dᴰ , F) → Functorᴰ F dᴰ) _
  FUNCTORᴰ .Hom[_][_,_] (f , fᴰ , α) =
    NatTransᴰ fᴰ α
  FUNCTORᴰ .idᴰ = idTransᴰ _
  FUNCTORᴰ ._⋆ᴰ_ = seqTransᴰ
  FUNCTORᴰ .⋆IdLᴰ αᴰ =
    makeNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆IdLᴰ _)
      (λ xᴰ → Dᴰᴰ.⋆IdLᴰ (αᴰ .N-obᴰ xᴰ))
  FUNCTORᴰ .⋆IdRᴰ  αᴰ =
    makeNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆IdRᴰ _)
      (λ xᴰ → Dᴰᴰ.⋆IdRᴰ (αᴰ .N-obᴰ xᴰ))
  FUNCTORᴰ .⋆Assocᴰ αᴰ βᴰ γᴰ =
    makeNatTransᴰPath (Dᴰ×C⇒Eᴰ.⋆Assocᴰ _ _ _)
      (λ xᴰ → Dᴰᴰ.⋆Assocᴰ (αᴰ .N-obᴰ xᴰ) (βᴰ .N-obᴰ xᴰ) (γᴰ .N-obᴰ xᴰ))
  FUNCTORᴰ .isSetHomᴰ = isSetNatTransᴰ _ _ _ _

  module _
    (D-⋆ : ∀ {x} → D.id D.⋆ D.id Eq.≡ D.id {x = x})
    (F-seq' : ∀ d dᴰ →
     {x y z : Liftω (Eobᴰ d)} (f : Hom[ fibEq Eᴰ D-⋆ d , x ] y)
      (g : Hom[ fibEq Eᴰ D-⋆ d , y ] z) →
      (Categoryᴰ.∫C (Dᴰ ×ᴰ Eᴰ) ⋆
       F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) f)
      (F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆) g)
      Eq.≡
      F-hom (fibᴰEqF D Dᴰ Eᴰ Dᴰᴰ d dᴰ D-⋆)
      ((fibEq Eᴰ D-⋆ d ⋆ f) g)) where
    private

      C⇒EqEᴰ : Categoryᴰ D (FunctorEq D-⋆) _
      C⇒EqEᴰ = FUNCTOR-EQ C Eᴰ D-⋆

      Dᴰ×C⇒EqEᴰ = Dᴰ ×ᴰ C⇒EqEᴰ
      module Dᴰ×C⇒EqEᴰ = CategoryᴰNotation Dᴰ×C⇒EqEᴰ

    FUNCTOR-EQᴰ :
      Categoryᴰ Dᴰ×C⇒EqEᴰ.∫C (λ (d , dᴰ , F) → FunctorEqᴰ D-⋆ (F-seq' _ _) F dᴰ) _
    FUNCTOR-EQᴰ =
      reindexEq F Xᴰ Eq.refl λ _ _ → Eq.refl
      where
      changeObs :
        Σω[ d ∈ Dob ] Σω[ dᴰ ∈ Dobᴰ d ] FunctorEq D-⋆ d →
        Σω[ d ∈ Dob ] Σω[ dᴰ ∈ Dobᴰ d ] Functor d
      changeObs (d , dᴰ , F) = d , dᴰ , FunctorEq→Functor D-⋆ d F

      X : Category _ _
      X = ChangeOfObjects Dᴰ×C⇒Eᴰ.∫C changeObs

      Xᴰ : Categoryᴰ X
        (λ (d , dᴰ , F) →
          FunctorEqᴰ D-⋆ (F-seq' _ _)
            F dᴰ) _
      Xᴰ = ChangeOfObjectsᴰ.ChangeOfObjectsᴰ FUNCTORᴰ
        λ {(d , dᴰ , F)} Fᴰ → FunctorEqᴰ→Functorᴰ D-⋆
          (F-seq' _ _) Fᴰ

      F : LocallySmallF.Functor Dᴰ×C⇒EqEᴰ.∫C X
      F .F-ob = λ z → z
      F .F-hom = λ z → z
      F .F-id = refl
      F .F-seq = λ _ _ → refl
