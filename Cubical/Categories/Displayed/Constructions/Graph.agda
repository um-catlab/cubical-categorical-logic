{-
  The graph category of a profunctor viewed as a displayed category over the product.
-}

{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Constructions.Graph where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor.Redundant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Base.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Preorder

private
  variable
    ℓC ℓC' ℓD ℓD' ℓS : Level

open Category
open Preorderᴰ
open Functor

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
         (R : Bifunctor C D (SET ℓS))
         where
  open Bifunctor

  Graph : Preorderᴰ (C ×C D) ℓS ℓS
  Graph .ob[_] (c , d) = ⟨ R ⟅ c , d ⟆b ⟩
  Graph .Hom[_][_,_] (f , g) r s = (R ⟪ f , g ⟫×) r ≡ s
  Graph .idᴰ = funExt⁻ (R .Bif-×-id) _
  Graph ._⋆ᴰ_ {f = f , g}{g = f' , g'} r s =
    funExt⁻ (R .Bif-×-seq f f' g g') _
    ∙ cong (R .Bif-hom× f' g') r
    ∙ s
  Graph .isPropHomᴰ {x = c , d}{y = c' , d'} = str (R ⟅ c' , d' ⟆b) _ _

  -- TODO: show Graph is a two-sided discrete fibration
  -- https://ncatlab.org/nlab/show/profunctor#in_terms_of_twosided_discrete_fibrations
