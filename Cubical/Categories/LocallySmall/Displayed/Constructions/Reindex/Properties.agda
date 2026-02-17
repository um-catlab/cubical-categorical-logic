{-# OPTIONS -W noUnsupportedIndexedMatch #-}
module Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma.More
import Cubical.Data.Equality as Eq

open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Functor.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Constructions.Reindex.Base

open Category
open Categoryᴰ
open Σω
open Liftω

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
  module _
    (C-⋆ : ∀ {x} → C.id C.⋆ C.id Eq.≡ C.id {x})
    (c : Cob)
    where
    fib→fibEq : Functor (fib Cᴰ c) (fibEq Cᴰ C-⋆ c)
    fib→fibEq .Functor.F-ob = λ z → z
    fib→fibEq .Functor.F-hom = λ z → z
    fib→fibEq .Functor.F-id =
      Cᴰ.rectify $ Cᴰ.≡out $
        sym $ Cᴰ.reind-filler _ _
    fib→fibEq .Functor.F-seq {x = x}{y = y}{z = z} f g =
      Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reind-filler _ _)
        ∙ Cᴰ.reindEq-pathFiller _ _

    -- fib→fibEq introduces a transport when acting on composition
    -- of morphisms
    module _ where
      private
        module Cᴰv = CategoryNotation (fib Cᴰ c)

        module _ {x y z} {f : Cᴰv.Hom[ x , y ]}{g : Cᴰv.Hom[ y , z ]} where
          _ : fib→fibEq .Functor.F-hom (f Cᴰv.⋆ g) ≡
                 transp (λ i → Cᴰ.Hom[ C.⋆IdR C.id i ][ x , z ]) i0 (f Cᴰ.⋆ᴰ g)
          _ = refl

    fibEq→fib :  Functor (fibEq Cᴰ C-⋆ c) (fib Cᴰ c)
    fibEq→fib .Functor.F-ob = λ z → z
    fibEq→fib .Functor.F-hom = λ z → z
    fibEq→fib .Functor.F-id =
      Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.reind-filler _ _
    fibEq→fib .Functor.F-seq f g =
      Cᴰ.rectify $ Cᴰ.≡out $
        (sym $ Cᴰ.reindEq-pathFiller _ _)
        ∙ Cᴰ.reind-filler _ _

    -- fibEq→fib is an Eq.transport on morphisms, which is very
    -- nice definitionally when C-⋆ is Eq.refl
    module _ where
      private
        module Cᴰv = CategoryNotation (fibEq Cᴰ C-⋆ c)

        module _ {x y z} {f : Cᴰv.Hom[ x , y ]}{g : Cᴰv.Hom[ y , z ]} where
          _ : fibEq→fib .Functor.F-hom (f Cᴰv.⋆ g) ≡
                Eq.transport Cᴰ.Hom[_][ x , z ] C-⋆ (f Cᴰ.⋆ᴰ g)
          _ = refl

    open Functor
    fibEq→fib→fibEq-F-hom :
      ∀ {x}{y} f → (fib→fibEq ∘F fibEq→fib) .F-hom {x = x}{y = y} f ≡ f
    fibEq→fib→fibEq-F-hom f = refl

    fib→fibEq→fib-F-hom :
      ∀ {x}{y} f → (fibEq→fib ∘F fib→fibEq) .F-hom {x = x}{y = y} f ≡ f
    fib→fibEq→fib-F-hom f = refl
