module Cubical.Categories.LocallySmall.Displayed.HLevels where

open import Cubical.Foundations.Prelude
-- open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
-- open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base

module _
  {C  : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where

  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ

  hasContrHoms : Typeω
  hasContrHoms =
    ∀ {c c' : Cob}(f : C.Hom[ c , c' ])
      (cᴰ : Cobᴰ c)(cᴰ' : Cobᴰ c')
      → isContr Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasPropHoms : Typeω
  hasPropHoms =
    ∀ {c c' : Cob}(f : C.Hom[ c , c' ])
      (cᴰ : Cobᴰ c)(cᴰ' : Cobᴰ c')
      → isProp Cᴰ.Hom[ f ][ cᴰ , cᴰ' ]

  hasContrHoms→hasPropHoms : hasContrHoms → hasPropHoms
  hasContrHoms→hasPropHoms contrHoms =
    λ f cᴰ cᴰ' → isContr→isProp (contrHoms f cᴰ cᴰ')

module _
       {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
       {F : Functor C D}
       {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
       {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
       where
  open Functor
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  module _
    (propHoms : hasPropHoms Dᴰ)
    where

    mkPropHomsFunctor :
        (F-obᴰ  : {x : Cob} → Cobᴰ x → Dobᴰ (F .F-ob x))
        → (F-homᴰ : {x y : Cob}
          {f : C.Hom[ x , y ]} {xᴰ : Cobᴰ x} {yᴰ : Cobᴰ y}
          → Cᴰ.Hom[ f ][ xᴰ , yᴰ ] → Dᴰ.Hom[ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
        → Functorᴰ F Cᴰ Dᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ = F-homᴰ
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
      Dᴰ.≡in {p = F-id F} (isProp→PathP (λ _ → propHoms _ _ _) _ _)
    mkPropHomsFunctor F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ _ _ =
      Dᴰ.≡in {p = F-seq F _ _} (isProp→PathP (λ _ → propHoms _ _ _) _ _)

  module _
    (contrHoms : hasContrHoms Dᴰ)
    where

    mkContrHomsFunctor :
      (F-obᴰ  : {x : Cob} → Cobᴰ x → Dobᴰ (F .F-ob x))
       → Functorᴰ F Cᴰ Dᴰ
    mkContrHomsFunctor F-obᴰ =
      mkPropHomsFunctor (hasContrHoms→hasPropHoms Dᴰ contrHoms) F-obᴰ
      λ _ → contrHoms _ _ _ .fst

module _
       {C : Category Cob CHom-ℓ} {D : Category Dob DHom-ℓ}
       {F : Functor C D}
       {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
       where
  open Functor
  private
    module C = CategoryNotation C
    module Dᴰ = Categoryᴰ Dᴰ
  mkPropHomsSection :
    (propHoms : hasPropHoms Dᴰ)
      → (F-obᴰ  : (x : Cob) → Dobᴰ (F .F-ob x))
      → (F-homᴰ : {x y : Cob}
        (f : C.Hom[ x , y ]) → Dᴰ.Hom[ F .F-hom f ][ F-obᴰ x , F-obᴰ y ])
      → Section F Dᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-obᴰ = F-obᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-homᴰ = F-homᴰ
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-idᴰ =
    Dᴰ.≡in {p = F-id F} $ isProp→PathP (λ i → propHoms _ _ _) _ _
  mkPropHomsSection propHoms F-obᴰ F-homᴰ .Section.F-seqᴰ _ _ =
    Dᴰ.≡in {p = F-seq F _ _} $ isProp→PathP (λ i → propHoms _ _ _) _ _

  mkContrHomsSection :
    (contrHoms : hasContrHoms Dᴰ)
      → (F-obᴰ  : (x : Cob) → Dobᴰ (F .F-ob x))
      → Section F Dᴰ
  mkContrHomsSection contrHoms F-obᴰ = mkPropHomsSection
    (hasContrHoms→hasPropHoms Dᴰ contrHoms)
    F-obᴰ
      λ {x}{y} f → contrHoms (F .F-hom f) (F-obᴰ x) (F-obᴰ y) .fst

  module _ {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ} where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    -- Alternate version: maybe Dᴰ.Hom[_][_,_] isn't always
    -- contractible, but it is in the image of F-obᴰ
    mkContrHomsFunctor'
      : (F-obᴰ  : {x : Cob} → Cobᴰ x → Dobᴰ (F .F-ob x))
      → (F-homᴰ : {x y : Cob}
        {f : C.Hom[ x , y ]} {xᴰ : Cobᴰ x} {yᴰ : Cobᴰ y}
      → Cᴰ.Hom[ f ][ xᴰ , yᴰ ]
      → isContr (Dᴰ.Hom[ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]))
      → Functorᴰ F Cᴰ Dᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-obᴰ = F-obᴰ
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-homᴰ fᴰ = F-homᴰ fᴰ .fst
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-idᴰ =
      Dᴰ.≡in {p = F-id F} $ symP (toPathP (isProp→PathP (λ i → isContr→isProp (F-homᴰ Cᴰ.idᴰ)) _ _))
    mkContrHomsFunctor' F-obᴰ F-homᴰ .Functorᴰ.F-seqᴰ fᴰ gᴰ =
      Dᴰ.≡in {p = F-seq F _ _} $ symP (toPathP (isProp→PathP
        (λ i → isContr→isProp (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ))) _ _))
