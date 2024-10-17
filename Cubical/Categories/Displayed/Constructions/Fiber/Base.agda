{-

  Given a functor F : C → D, we can construct a displayed category
  using the fibers of F.ob, F.hom.

  This should have the property that a Section of Fiber F is
  equivalent to an actual section of the functor F.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Fiber.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Instances.Path
open import Cubical.Categories.Displayed.Constructions.Weaken
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL
open import Cubical.Categories.Displayed.Constructions.Reindex.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Functor
open Categoryᴰ
module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D)
  where

  opaque
    Fiber : Categoryᴰ D (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
    Fiber = ∫Cᴰsl {D = C}
      (reindex (PathC D) (F ×F Id {C = D}))

    πCᴰ : Functorᴰ Id Fiber (weaken D C)
    πCᴰ = {!!} ∘Fᵛᴰ Fstᴰsl ((reindex (PathC D) (F ×F Id {C = D})))

  private
    module Fiber = Categoryᴰ Fiber
    opaque
      unfolding Fiber
      test-ob : ∀ {d} → Fiber.ob[ d ] ≡ fiber (F .F-ob) d
      test-ob = refl

      -- need to make this so that test-hom has a well-defined type
      -- outside the opaque block
      test-hom-ty : ∀ {d d'}(f : D [ d , d' ])(dᴰ : Fiber.ob[ d ])
        (dᴰ' : Fiber.ob[ d' ]) → Type (ℓ-suc (ℓ-max ℓC' ℓD'))
      test-hom-ty f dᴰ dᴰ' = Fiber.Hom[ f ][ dᴰ , dᴰ' ]
          ≡ (Σ[ fᴰ ∈ C [ dᴰ .fst , dᴰ' .fst ] ]
            PathP (λ i → D [ dᴰ .snd i , dᴰ' .snd i ]) (F ⟪ fᴰ ⟫) f)

      test-hom : ∀ {d d'}{f : D [ d , d' ]}{dᴰ dᴰ'} → test-hom-ty f dᴰ dᴰ'
      test-hom = refl

  private
    ∫Fiber = ∫C Fiber
  πC : Functor ∫Fiber C
  πC = weakenΠ D C ∘F ∫F {F = Id} ({!!} ∘Fᵛᴰ {!Fstᴰsl!})

  πPath : F ∘F πC ≡ TotalCat.Fst {Cᴰ = Fiber}
  πPath = {!!}
