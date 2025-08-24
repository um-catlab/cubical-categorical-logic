-- Free category generated from base objects and generators

-- This time using a "quiver" as the presentation of the generators,
-- which is better in some applications

module Cubical.Categories.Constructions.Free.Category.UniversalProperty where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Quiver.Base as Quiver
open import Cubical.Data.Graph.Base as Graph
open import Cubical.Data.Graph.Displayed as Graph hiding (Section)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct as BP
open import Cubical.Categories.UnderlyingGraph hiding (Interp)
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Path
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Constructions.Weaken.Base as Wk

open import Cubical.Categories.Displayed.Section.Base as Cat
open import Cubical.Categories.Constructions.Free.Category.Quiver

private
  variable
    ℓc ℓc' ℓd ℓd' ℓg ℓg' ℓh ℓh' ℓj ℓ : Level
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open Section
open HetSection
open QuiverOver

module _ (Q : Quiver ℓg ℓg') (C : Category ℓc ℓc') (ı : Interp Q C) where
  module _ {ℓd ℓd'} (Cᴰ : Categoryᴰ C ℓd ℓd') (ıᴰ : Interpᴰ Q ı Cᴰ) where
    private
      module Cᴰ = Categoryᴰ Cᴰ

    extends : GlobalSection Cᴰ → Type _
    extends S =
      Σ[ p ∈ (∀ q → (ıᴰ $gᴰ q) ≡ S .F-obᴰ (ı $g q)) ]
      (∀ g → PathP (λ i → Cᴰ [ ı <$g> g ][ p (Q .snd .dom g) i , p (Q .snd .cod g) i ])
               (ıᴰ <$g>ᴰ g)
               (S .F-homᴰ (ı <$g> g)))

  isFreeCategory : Typeω
  isFreeCategory = ∀ {ℓd ℓd' : Level}
    → (Cᴰ : Categoryᴰ C ℓd ℓd')
    → (ıᴰ : Interpᴰ Q ı Cᴰ)
    → Σ (GlobalSection Cᴰ) (extends Cᴰ ıᴰ)
