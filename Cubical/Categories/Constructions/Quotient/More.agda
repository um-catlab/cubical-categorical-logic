-- Quotient category
{-# OPTIONS --safe #-}

module Cubical.Categories.Constructions.Quotient.More where

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Initial
open import Cubical.Foundations.HLevels
import      Cubical.Data.Equality as Eq
open import Cubical.Foundations.Prelude
open import Cubical.HITs.SetQuotients as SetQuotients
  renaming ([_] to ⟦_⟧) hiding (elim)

open import Cubical.Categories.Constructions.Quotient
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Constructions.Reindex

private
  variable
    ℓ ℓ' ℓq ℓD ℓD' : Level

module _ (C : Category ℓ ℓ') where
  open Category C

  module _ (_~_ : {x y : ob} (f g : Hom[ x , y ] ) → Type ℓq)
           (~refl : {x y : ob} (f : Hom[ x , y ] ) → f ~ f)
           (~cong : {x y z : ob}
                    (f f' : Hom[ x , y ]) → f ~ f'
                  → (g g' : Hom[ y , z ]) → g ~ g'
                  → (f ⋆ g) ~ (f' ⋆ g')) where
    private
      C/~ = QuotientCategory C _~_ ~refl ~cong
      QF = QuoFunctor C _~_ ~refl ~cong

    open Categoryᴰ
    module _ (Dᴰ : Categoryᴰ C/~ ℓD ℓD') where
      private
        module Dᴰ = Categoryᴰ Dᴰ

      -- TODO: make a macro that applies to Eq.refl in exactly this way
      reindexᴰQuo : Categoryᴰ C ℓD ℓD'
      reindexᴰQuo = reindex' Dᴰ QF Eq.refl λ _ _ → Eq.refl

      open Section
      elim : (F : Section reindexᴰQuo)
           → (∀ {x y} → (f g : Hom[ x , y ]) → (p : f ~ g) →
             PathP (λ i → Dᴰ.Hom[ eq/ f g p i ][ F .F-ob x , F .F-ob y ])
                   (F .F-hom f)
                   (F .F-hom g))
           → Section Dᴰ
      elim F F-resp-∼ .F-ob = F .F-ob
      elim F F-resp-∼ .F-hom = SetQuotients.elim (λ _ → Dᴰ.isSetHomᴰ)
        (F .F-hom)
        F-resp-∼
      elim F F-resp-∼ .F-id = F .F-id
      elim F F-resp-∼ .F-seq =
        elimProp2 (λ [f] [g] → Dᴰ.isSetHomᴰ _ _) (F .F-seq)
