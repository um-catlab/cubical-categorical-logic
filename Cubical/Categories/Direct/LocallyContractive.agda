{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.LocallyContractive {ℓ ℓ' ℓD : Level} {C : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'} (dir : DirectStr C Wo) where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Functor using (Functor ; _∘F_)
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Displayed.Instances.FunctorAlgebras.Recursive
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Functors.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.StrictHom.Self

open Functor
open PshHomStrict

open Category C using (ob ; id ; _⋆_ ; ⋆IdL)
open DirectNotation dir using (_≺_)


private
  ℓ▷ : Level
  ℓ▷ = ℓ-max ℓ ℓ'

  infixr 5 _⇒_
  _⇒_ : Presheaf C ℓ▷ → Presheaf C ℓ▷ → Presheaf C ℓ▷
  X ⇒ Y = X ⇒PshLargeStrict Y

▷HomActionPsh : (Presheaf C ℓ▷ → Presheaf C ℓ▷) → Type _
▷HomActionPsh F₀ =
  {X Y : Presheaf C ℓ▷} → PshHomStrict (▷ .F-ob (X ⇒ Y)) (F₀ X ⇒ F₀ Y)

private
  nm : {X Y : Presheaf C ℓ▷} (h : PshHomStrict X Y) (y : ob)
     → ⟨ (X ⇒ Y) .F-ob y ⟩
  nm h y .N-ob d (f , ξ) = h .N-ob d ξ
  nm h y .N-hom d' d g (f' , ξ') (f , ξ) e =
    h .N-hom d' d g ξ' ξ (cong snd e)

open EnrichedFunctor renaming (F-hom to FE-hom; F-ob to FE-ob)

private
  PShStrongFunctor : Type _
  PShStrongFunctor = EnrichedFunctor (PshMon.𝓟Mon C ℓ) (self C ℓ) (self C ℓ)

isContractiveHomAction :
  (F : PShStrongFunctor)
  → ▷HomActionPsh (F .FE-ob) → Type _
isContractiveHomAction F G =
  {X Y : Presheaf C ℓ▷}
  → F .FE-hom ≡ (next (X ⇒ Y)) ⋆PshHomStrict G {X} {Y}

isLocallyContractive : (F : PShStrongFunctor) → Type (ℓ-suc (ℓ-max ℓ ℓ'))
isLocallyContractive F =
   Σ[ G ∈ ▷HomActionPsh (F .FE-ob) ]
   isContractiveHomAction F G
