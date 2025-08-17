{- Functors of SCwFs. These come in variants depending on whether the extension is preserved. -}
{-# OPTIONS --safe #-}
module Cubical.Categories.WithFamilies.Simple.Functor where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.WithFamilies.Simple.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

module _ (C : SCwF ℓC ℓC' ℓT ℓT')(D : SCwF ℓD ℓD' ℓS ℓS') where
  -- A PreFunctor is not required to preserve the terminal ctx or comprehensions
  PreFunctor : Type _
  PreFunctor =
    Σ[ F ∈ Functor (C .fst) (D .fst) ]
    Σ[ F-ty ∈ (C .snd .fst → D .snd .fst) ]
    ∀ {A} → PshHet F (C .snd .snd .fst A) (D .snd .snd .fst (F-ty A))
