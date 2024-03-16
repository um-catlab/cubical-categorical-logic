{-

  The "simple" total displayed category, the special case of the
  displayed total category where the base is a product rather than a
  ∫C. With the current definitions, C ×C D is definitionally equal to
  ∫C C (weaken C D) so this is just a type specialization of ∫Cᴰ

  If in the future we add --no-eta-equality to Categories then this
  could instead be defined using reindexing along the equivalence
  between C ×C D and ∫C C (weaken C D) instead, as we have to do with
  SimpleTotalCategoryL.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryR where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More
open import Cubical.Categories.Functor

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Constructions.Reindex as Reindex
  hiding (intro)
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk
  hiding (intro)
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Terminal hiding (intro)
open import Cubical.Categories.Displayed.Base.More as TotalCat

private
  variable
    ℓB ℓB' ℓBᴰ ℓBᴰ' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

open Categoryᴰ

-- Given a displayed category over a product of two categories,
-- we can project out the two categories and
-- then display over them.
module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (Cᴰ : Categoryᴰ (C ×C D) ℓCᴰ ℓCᴰ')
  where
  open Category

  private
    module Cᴰ = Categoryᴰ Cᴰ

  -- s for "simple" because D is not dependent on C
  -- r for "right" because D is on the right of the product
  ∫Cᴰsr : Categoryᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫Cᴰsr = ∫Cᴰ (weaken C D) Cᴰ

  Fstᴰsr : Functorᴰ Id ∫Cᴰsr (weaken C D)
  Fstᴰsr = Fstᴰ Cᴰ

  -- TODO: Sndᴰsr

  module _
    {E : Category ℓE ℓE'}
    (F : Functor E C)
    {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
    (Fᴰ : Functorᴰ F Eᴰ (weaken C D))
    (Gᴰ : Functorᴰ (∫F Fᴰ) (Unitᴰ (∫C Eᴰ)) Cᴰ)
    where

    open Functorᴰ

    intro : Functorᴰ F Eᴰ ∫Cᴰsr
    intro = mk∫ᴰFunctorᴰ Cᴰ F Fᴰ Gᴰ

  -- ∀ c , d . Cᴰ (c , d) → Σ[ d' ] Cᴰ (c , d')
  -- This can be defined more generally for ∫Cᴰ
  Assocᴰsr : Functorᴰ (BP.Fst C D) Cᴰ ∫Cᴰsr
  Assocᴰsr = intro _ (Wk.intro (BP.Fst C D) (BP.Snd C D))
    (reindF' _ Eq.refl Eq.refl TotalCat.Snd)

  -- Σ[ c ] Σ[ d ] Cᴰ (c , d) → Σ[ cd ] Cᴰ cd
  Assoc-sr⁻ : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)
  Assoc-sr⁻ = Assocᴰ {Cᴰ = weaken C D} Cᴰ
