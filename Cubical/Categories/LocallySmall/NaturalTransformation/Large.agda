module Cubical.Categories.LocallySmall.NaturalTransformation.Large where


open import Cubical.Data.Sigma


open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Functor.Base
open import Cubical.Categories.LocallySmall.Variables

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open Category
open Categoryᴰ

-- The type of natural transformations between functors of locally
-- small categories is large because while each D.Hom[_,_] is small,
-- they can each be in a different universe, the natural
-- transformations have to be in the universe ⨆_x Hom-ℓ (F x) (G x),
-- which is ω.

-- This means we do *not* get a locally small category of functors
-- between arbitrary locally small categories, only a large category.
record NatTrans {C : Category Cob CHom-ℓ}{D : Category Dob DHom-ℓ}
  (F G : Functor C D) : Typeω
  where
  no-eta-equality
  constructor natTrans
  private
    module F = FunctorNotation F
    module G = FunctorNotation G
    module C = CategoryNotation C
    module D = CategoryNotation D
  field
    N-ob : ∀ x → D.Hom[ F.F-ob x , G.F-ob x ]
    N-hom : ∀ {x y}(f : C.Hom[ x , y ])
      → (F.F-hom f D.⋆ N-ob y) ≡ (N-ob x D.⋆ G.F-hom f)
