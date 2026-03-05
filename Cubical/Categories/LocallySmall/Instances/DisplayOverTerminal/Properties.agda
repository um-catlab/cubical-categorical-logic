module Cubical.Categories.LocallySmall.Instances.DisplayOverTerminal.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Instances.Unit
open import Cubical.Categories.LocallySmall.Instances.DisplayOverTerminal.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Notation
open import Cubical.Categories.LocallySmall.Displayed.Instances.Reindex.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Base
open import Cubical.Categories.LocallySmall.Displayed.Functor.Properties

open Category

module _ where
  open CategoryVariables
  module _
    (Cᴰ : Categoryᴰ UNIT Cobᴰ CHom-ℓᴰ) where
    private
      module Cᴰ = CategoryᴰNotation Cᴰ

    CatᴰOverUNIT→Fib : Functor (CatᴰOverUNIT→Cat Cᴰ) Cᴰ.v[ _ ]
    CatᴰOverUNIT→Fib .Functor.F-ob = λ z → z
    CatᴰOverUNIT→Fib .Functor.F-hom = λ z → z
    CatᴰOverUNIT→Fib .Functor.F-id = sym $ transportRefl _
    CatᴰOverUNIT→Fib .Functor.F-seq _ _ = sym $ transportRefl _

    CatᴰOverUNIT→FibEq : Functor (CatᴰOverUNIT→Cat Cᴰ) (fibEq Cᴰ Eq.refl _)
    CatᴰOverUNIT→FibEq .Functor.F-ob = λ z → z
    CatᴰOverUNIT→FibEq .Functor.F-hom = λ z → z
    CatᴰOverUNIT→FibEq .Functor.F-id = refl
    CatᴰOverUNIT→FibEq .Functor.F-seq _ _ = refl

    ∫→CatᴰOverUNIT : Functor Cᴰ.∫C (CatᴰOverUNIT→Cat Cᴰ)
    ∫→CatᴰOverUNIT .Functor.F-ob = λ z → z .Σω.snd
    ∫→CatᴰOverUNIT .Functor.F-hom = λ z → z .snd
    ∫→CatᴰOverUNIT .Functor.F-id = refl
    ∫→CatᴰOverUNIT .Functor.F-seq = λ _ _ → refl

    module _
      {D : Category Dob DHom-ℓ}
      {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
      {d : Dob}
      (Fᴰ : Functorᴰ introUNIT Dᴰ Cᴰ)
      where
      private
        module Dᴰ = CategoryᴰNotation Dᴰ

      CatᴰOverUNIT-intro : Functor Dᴰ.∫C (CatᴰOverUNIT→Cat Cᴰ)
      CatᴰOverUNIT-intro = ∫→CatᴰOverUNIT ∘F Functorᴰ.∫F Fᴰ

    module _
      {D : Category Dob DHom-ℓ}
      {Dᴰ : Categoryᴰ D Dobᴰ DHom-ℓᴰ}
      {d : Dob}
      (Fᴰ : Functorᴰ (elimUNIT d) Cᴰ Dᴰ)
      where
      private
        module Dᴰ = CategoryᴰNotation Dᴰ

      CatᴰOverUNIT-elim : Functor (CatᴰOverUNIT→Cat Cᴰ) Dᴰ.v[ d ]
      CatᴰOverUNIT-elim =
        Fv Fᴰ (liftω tt) ∘F CatᴰOverUNIT→Fib
