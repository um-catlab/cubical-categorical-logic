module Cubical.Categories.LocallySmall.Displayed.Functor.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
-- open import Cubical.Foundations.HLevels
-- open import Cubical.Foundations.HLevels.More

-- open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
-- open import Cubical.Categories.LocallySmall.Category.Small
open import Cubical.Categories.LocallySmall.Variables.Category
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Functor.Properties

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
-- open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Displayed.Category.Properties
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base

open Σω
open CatIso
open CatIsoᴰ
open Functor

module _ where
  open CategoryVariables
  module _
    {F : Functor C D}
    {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
    {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    where
    private
      module C = CategoryNotation C
      module D = CategoryNotation D
      module Cᴰ = CategoryᴰNotation Cᴰ
      module Dᴰ = CategoryᴰNotation Dᴰ
      module F = FunctorNotation F
    open Functorᴰ Fᴰ

    F-isoᴰ : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
        (fᴰ : Cᴰ.ISOCᴰ.Hom[ f ][ xᴰ , yᴰ ])
        → Dᴰ.ISOCᴰ.Hom[ F.F-ISO.F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]
    F-isoᴰ fᴰ .funᴰ = F-homᴰ (fᴰ .funᴰ)
    F-isoᴰ fᴰ .invᴰ = F-homᴰ (fᴰ .invᴰ)
    F-isoᴰ fᴰ .secᴰ = sym (F-seqᴰ (fᴰ .invᴰ) (fᴰ .funᴰ)) ∙ F-homᴰ⟨ fᴰ .secᴰ ⟩ ∙ F-idᴰ
    F-isoᴰ fᴰ .retᴰ = sym (F-seqᴰ (fᴰ .funᴰ) (fᴰ .invᴰ)) ∙ F-homᴰ⟨ fᴰ .retᴰ ⟩ ∙ F-idᴰ

open Functorᴰ
module _ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  where

  private
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module F = FunctorNotation F

  F-Isoᴰ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → Functorᴰ F.F-ISO Cᴰ.ISOCᴰ Dᴰ.ISOCᴰ
  F-Isoᴰ Fᴰ .F-obᴰ = Fᴰ .F-obᴰ
  F-Isoᴰ Fᴰ .F-homᴰ = F-isoᴰ Fᴰ
  F-Isoᴰ Fᴰ .F-idᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-idᴰ)
  F-Isoᴰ Fᴰ .F-seqᴰ fᴰ gᴰ = Dᴰ.ISOCᴰ≡ (Fᴰ .F-seqᴰ (fᴰ .funᴰ) (gᴰ .funᴰ))

  module FunctorᴰNotation (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where
    open Functor (∫F Fᴰ) public -- should this be FunctorNotation?
    open Functorᴰ Fᴰ public

    F-ISOᴰ = F-Isoᴰ Fᴰ
    module F-ISOᴰ = Functorᴰ F-ISOᴰ

module _ {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ}
  {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  (c : Cob)
  where
  private
    module C = CategoryNotation C
    module D = CategoryNotation D
    module Cᴰ = CategoryᴰNotation Cᴰ
    module Dᴰ = CategoryᴰNotation Dᴰ
    module F = FunctorNotation F
    module Fᴰ = FunctorᴰNotation Fᴰ

  Fv : Functor Cᴰ.v[ c ] Dᴰ.v[ F.F-ob c ]
  Fv .F-ob = Fᴰ.F-obᴰ
  Fv .F-hom fᴰ = Dᴰ.reind F.F-id $ Fᴰ.F-homᴰ fᴰ
  Fv .F-id =
    Dᴰ.rectify $ Dᴰ.≡out $
      (sym $ Dᴰ.reind-filler _ _)
      ∙ Fᴰ.F-hom⟨ sym $ Cᴰ.reind-filler _ _ ⟩
      ∙ Fᴰ.F-idᴰ
      ∙ Dᴰ.reind-filler _ _
  Fv .F-seq fᴰ gᴰ =
    Dᴰ.rectify $ Dᴰ.≡out $
      (sym $ Dᴰ.reind-filler _ _)
      ∙ Fᴰ.F-homᴰ⟨ (sym $ Cᴰ.reind-filler _ _) ⟩
      ∙ Fᴰ.F-seqᴰ _ _
      ∙ Dᴰ.⟨ Dᴰ.reind-filler _ _ ⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
      ∙ Dᴰ.reind-filler _ _

module _ where
  open CategoryᴰVariables
  _^opFᴰ : {F : Functor C D} →
           {Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ} →
           {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ} →
           Functorᴰ F Cᴰ Dᴰ →
           Functorᴰ (F ^opF) (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  (Fᴰ ^opFᴰ) .F-obᴰ = F-obᴰ Fᴰ
  (Fᴰ ^opFᴰ) .F-homᴰ = F-homᴰ Fᴰ
  (Fᴰ ^opFᴰ) .F-idᴰ = F-idᴰ Fᴰ
  (Fᴰ ^opFᴰ) .F-seqᴰ = λ fᴰ gᴰ → F-seqᴰ Fᴰ gᴰ fᴰ
