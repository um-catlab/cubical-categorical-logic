module Cubical.Categories.LocallySmall.Constructions.Total.Properties where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Section.Base

open Category
open Categoryᴰ
open Σω


module _ {C : Category Cob CHom-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = CategoryᴰNotation Cᴰ

  module _ {D : Category Dob DHom-ℓ}
    (F : Functor D C) (Fᴰ : Section F Cᴰ) where

    intro : Functor D Cᴰ.∫C
    intro .Functor.F-ob = λ z → Functor.F-ob F z , Section.F-obᴰ Fᴰ z
    intro .Functor.F-hom = λ z → Functor.F-hom F z , Section.F-homᴰ Fᴰ z
    intro .Functor.F-id = Section.F-idᴰ Fᴰ
    intro .Functor.F-seq = Section.F-seqᴰ Fᴰ

  module _ {D : Category Dob DHom-ℓ}
    {F : Functor C D}
    {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where

    private
      module Dᴰ = CategoryᴰNotation Dᴰ

    elim : Section (F ∘F Cᴰ.Fst) Dᴰ
    elim = compFunctorᴰSection Fᴰ Cᴰ.Snd

  module _ {D : Category Dob DHom-ℓ}
    {F : Functor C D}
    {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
    (Fᴰ : Section (F ∘F Cᴰ.Fst) Dᴰ) where

    open Functorᴰ
    recᴰ : Functorᴰ F Cᴰ Dᴰ
    recᴰ .F-obᴰ = λ z → Section.F-obᴰ Fᴰ (_ , z)
    recᴰ .F-homᴰ = λ fᴰ → Section.F-homᴰ Fᴰ (_ , fᴰ)
    recᴰ .F-idᴰ = Section.F-idᴰ Fᴰ
    recᴰ .F-seqᴰ = λ fᴰ gᴰ → Section.F-seqᴰ Fᴰ (_ , fᴰ) (_ , gᴰ)
