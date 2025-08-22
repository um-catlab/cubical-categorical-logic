{-

  Given a functor F : C → D, the IsoFiber, also called the "weak
  fiber" is the displayed category over D whose objects over d are
  given by pairs of an object of c and an iso F c ≅ d.

  The universal property is that a GlobalSection of the IsoFiber of F
  is equivalent to a section of F up to isomorphism.

-}
module Cubical.Categories.Displayed.Constructions.IsoFiber.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Arrow.Base
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.Reindex.Base
open import Cubical.Categories.Displayed.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR
open import Cubical.Categories.Constructions.TotalCategory hiding (Fst; Snd)
open import Cubical.Categories.Bifunctor hiding (Fst; Snd)

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D)
  where

  IsoFiber : Categoryᴰ D (ℓ-max ℓC ℓD') (ℓ-max ℓC' ℓD')
  IsoFiber = ∫Cᴰsr {D = C}
    (reindex (Iso D) (Id {C = D} ×F F))

  IsoFiberReflection : GlobalSection IsoFiber
    → Σ[ F⁻ ∈ Functor D C ] (F ∘F F⁻) ≅ᶜ Id
  IsoFiberReflection S = F⁻ , i where
    F⁻ = introS⁻ _ S .fst
    i~ = symNatIso
      (IsoReflection' (compFunctorᴰSection (π _ _) (introS⁻ _ S .snd)))
    i : F ∘F F⁻ ≅ᶜ Id
    open NatTrans
    open NatIso
    open isIso
    i .trans .N-ob = i~ .trans .N-ob
    i .trans .N-hom = i~ .trans .N-hom
    i .nIso = i~ .nIso
