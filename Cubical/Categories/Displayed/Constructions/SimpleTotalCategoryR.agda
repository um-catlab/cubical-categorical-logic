


{-
  The "simple" total category is the same as the displayed total
  category, but where the input is displayed over the cartesian
  product C ×C D . This is equivalent to being displayed over
  ∫C {C} (weaken C D) but for now at least these are not
  definitionally equal, and so this is defined by a reindex.

  They are definitionally equal if Categories have eta equality
  or if the cartesian product were refactored to be defined as
  ∫C {C} (weaken C D).
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
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq as Reindex

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Reasoning
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk
  hiding (introS; introF; introS⁻)
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Constructions.TotalCategory as TotalCat
  hiding (intro)
import Cubical.Categories.Displayed.Constructions.TotalCategory
  as ∫ᴰ
  hiding (introS)
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
    module Cᴰ' =
      EqReindex {C = ∫C (weaken C D)} Cᴰ (TotalCat.Fst ,F weakenΠ _ _)
        Eq.refl (λ _ _ → Eq.refl)

  -- s for "simple" because D is not dependent on C
  -- r for "right" because D is on the right of the product
  ∫Cᴰ : Categoryᴰ C (ℓ-max ℓD ℓCᴰ) (ℓ-max ℓD' ℓCᴰ')
  ∫Cᴰ = ∫ᴰ.∫Cᴰ (weaken C D) Cᴰ'.reindex

  private
    module ∫Cᴰ = Categoryᴰ ∫Cᴰ
    test-ob : ∀ {c} → ∫Cᴰ.ob[ c ] ≡ (Σ[ d ∈ _ ] Cᴰ.ob[ c , d ])
    test-ob = refl

    test-hom : ∀ {c c' d d' cdᴰ cdᴰ'}{f : C [ c , c' ]} →
      ∫Cᴰ [ f ][ (d , cdᴰ ) , (d' , cdᴰ') ]
      ≡ (Σ[ g ∈ _ ] Cᴰ [ f , g ][ cdᴰ , cdᴰ' ])
    test-hom = refl

  Fstᴰ : Functorⱽ ∫Cᴰ (weaken C D)
  Fstᴰ = ∫ᴰ.Fstᴰ _

  -- -- TODO: Sndᴰsr

  -- module _
  --   {E : Category ℓE ℓE'}
  --   (F : Functor E C)
  --   (Fᴰ : Section F (weaken C D))
  --   (Gᴰ : Section (TotalCat.intro F Fᴰ) Cᴰ)
  --   where

  --   open Functorᴰ

  --   introS : Section F ∫Cᴰ
  --   introS = ?
  --   introS = TotalCatᴰ.introS {C = C}{Cᴰ = weaken C D} Cᴰ F Fᴰ Gᴰ

  module _
    where
    open Functor
    open Section
    introS⁻ : GlobalSection ∫Cᴰ →
      Σ[ F ∈ Functor C D ]
      Section (Id ,F F) Cᴰ
    introS⁻ S .fst .F-ob z = S .F-obᴰ z .fst
    introS⁻ S .fst .F-hom f = S .F-homᴰ f .fst
    introS⁻ S .fst .F-id = cong fst (S .F-idᴰ)
    introS⁻ S .fst .F-seq _ _ = cong fst (S .F-seqᴰ _ _)
    introS⁻ S .snd .F-obᴰ z = S .F-obᴰ z .snd
    introS⁻ S .snd .F-homᴰ f = S .F-homᴰ f .snd
    introS⁻ S .snd .F-idᴰ = cong snd (S .F-idᴰ)
    introS⁻ S .snd .F-seqᴰ _ _ = cong snd (S .F-seqᴰ _ _)

  -- -- ∀ c , d . Cᴰ (c , d) → Σ[ d' ] Cᴰ (c , d')
  -- -- This can be defined more generally for ∫Cᴰ
  -- -- Assocᴰsr : Functorᴰ (BP.Fst C D) Cᴰ ∫Cᴰsr
  -- -- Assocᴰsr = intro _ (Wk.intro (BP.Fst C D) (BP.Snd C D))
  -- --   (reindF' _ Eq.refl Eq.refl TotalCat.Snd)

  -- -- Σ[ c ] Σ[ d ] Cᴰ (c , d) → Σ[ cd ] Cᴰ cd
  -- Assoc : Functor (∫C ∫Cᴰsr) (∫C Cᴰ)
  -- Assoc = Assocᴰ {Cᴰ = weaken C D} Cᴰ
