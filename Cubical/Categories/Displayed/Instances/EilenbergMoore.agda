-- The Eilenberg–Moore category of a monad
module Cubical.Categories.Displayed.Instances.EilenbergMoore where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monad.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebras
open import Cubical.Categories.Displayed.Instances.StructureOver
open import Cubical.Categories.Instances.TotalCategory

private
  variable ℓC ℓC' : Level

module _ {C : Category ℓC ℓC'} (Mon : Monad C) where

  private
    module C = Category C
    module M = IsMonad (snd Mon)
    module FT = Functor (fst Mon)
  open NatTrans

  -- The conditions needed to upgrade an algebra of an endofunctor to
  -- an algebra of a monad
  --   α ∘ η x ≡ id          (unit law)
  --   α ∘ μ x ≡ α ∘ T α     (multiplication law)
  EMStructureOver : StructureOver (∫C (ALGᴰ (fst Mon))) ℓC' ℓ-zero
  StructureOver.ob[_] EMStructureOver (x , α) =
    (M.η .N-ob x C.⋆ α ≡ C.id)
      × (M.μ .N-ob x C.⋆ α ≡ FT.F-hom α C.⋆ α)
  StructureOver.Hom[_][_,_] EMStructureOver _ _ _ = Unit
  StructureOver.idᴰ EMStructureOver = tt
  StructureOver._⋆ᴰ_ EMStructureOver _ _ = tt
  StructureOver.isPropHomᴰ EMStructureOver = isPropUnit

  EMᴰ : Categoryᴰ (∫C (ALGᴰ (fst Mon))) ℓC' ℓ-zero
  EMᴰ = StructureOver→Catᴰ EMStructureOver

  -- The Eilenberg–Moore category.
  EM : Category (ℓ-max ℓC ℓC') (ℓ-max ℓC' ℓC')
  EM = ∫C EMᴰ

-- A morphism of algebras is determined by the carrier map
module _ {C : Category ℓC ℓC'} {Mon : Monad C} where

  emHom≡ : {X Y : Category.ob (EM Mon)}
    {f g : EM Mon [ X , Y ]}
    → f .fst .fst ≡ g .fst .fst → f ≡ g
  emHom≡ p = ΣPathP
    (Σ≡Prop
      (λ _ → hasPropHomsStructureOver (AlgStructureOver (fst Mon)) _ _ _) p
    , refl)
