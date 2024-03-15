{-

  The slice category over a displayed category. Used in the definition
  of a fibration.

-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Slice where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.Constructions.BinProduct.More as BP
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Displayed.Base as Disp
open import Cubical.Categories.Displayed.Constructions.Weaken as Wk
open import Cubical.Categories.Displayed.Constructions.Reindex as Reindex
open import Cubical.Categories.Displayed.BinProduct
open import Cubical.Categories.Displayed.Constructions.BinProduct.More as BPᴰ
open import Cubical.Categories.Displayed.Properties as Disp
open import Cubical.Categories.Displayed.Base.More as Disp
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Base.DisplayOverProjections
open import Cubical.Categories.Displayed.Instances.Hom
open import Cubical.Categories.Displayed.Instances.Terminal as Unitᴰ
open import Cubical.Categories.Displayed.Base.HLevel1Homs
open import Cubical.Categories.Displayed.Reasoning
private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor

module _ (C : Category ℓC ℓC') (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  -- See test below for the intuitive definition
  _/C_ : Categoryᴰ C _ _
  _/C_ = ∫Cᴰ (weaken C C) (Cᴰ' ×ᴰ Hom C)
    where Cᴰ' = (reindex' Cᴰ (BP.Snd C C) Eq.refl λ _ _ → Eq.refl)
   -- TODO: wanted: a macro for the      Eq.refl λ _ _ → Eq.refl above

  private
    open Category
    open Categoryᴰ
    test : ∀ {c} → _/C_ .ob[_] c ≡ (Σ[ c' ∈ C .ob ] Cᴰ .ob[_] c' × C [ c , c' ])
    test = refl

  Δ/C : Functorᴰ Id Cᴰ _/C_
  Δ/C = mk∫ᴰFunctorᴰ _ Id (Wk.intro Id Id)
    (BPᴰ.intro _
      (Reindex.intro' F (reindF' _ Eq.refl Eq.refl (Disp.Snd {Cᴰ = Cᴰ})))
      Fᴰ')
    where
      F = (∫F {Cᴰ = Cᴰ} (Wk.intro Id Id))
      G = funcComp (Δ C) (Disp.Fst {Cᴰ = Cᴰ})
      Gᴰ : Functorᴰ G (Unitᴰ (∫C Cᴰ)) (Hom C)
      Gᴰ = (ID {C = C} ∘Fᴰ Unitᴰ.intro (Disp.Fst {Cᴰ = Cᴰ}))

      Fᴰ' : Functorᴰ F (Unitᴰ (∫C Cᴰ)) (Hom C)
      Fᴰ' = reindF' _ Eq.refl Eq.refl Gᴰ

  private
    open Functorᴰ
    _ : ∀ c (cᴰ : Cᴰ .ob[_] c) → Δ/C .F-obᴰ cᴰ ≡ (c , (cᴰ , C .id))
    _ = λ c cᴰ → refl
