{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.More

-- There are multiple definitions of terminal object in a displayed category:
-- 1. A terminal object in the total category, which is preserved by projection
-- 2. A terminal object in the *fiber* of an object

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP : Level

open Category
open Categoryᴰ
open Functorᴰ
open Iso
open isIsoOver

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  TerminalPresheafᴰ : (P : Presheaf C ℓP) → Presheafᴰ Cᴰ P ℓ-zero
  TerminalPresheafᴰ P .F-obᴰ x x₁ = Unit , isSetUnit
  TerminalPresheafᴰ P .F-homᴰ = λ _ x _ → tt
  TerminalPresheafᴰ P .F-idᴰ i = λ x x₁ → tt
  TerminalPresheafᴰ P .F-seqᴰ fᴰ gᴰ i = λ x _ → tt

  -- Terminal object over a terminal object
  -- TODO: refactor using Constant Functorᴰ eventually
  TerminalᴰSpec : Presheafᴰ Cᴰ (TerminalPresheaf {C = C}) ℓ-zero
  TerminalᴰSpec = TerminalPresheafᴰ _

  Terminalᴰ : (term : Terminal' C) →
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  Terminalᴰ term = UniversalElementᴰ _ TerminalᴰSpec term

  module TerminalᴰNotation {term' : Terminal' C}
    (termᴰ : Terminalᴰ term') where

    open UniversalElement
    open UniversalElementᴰ termᴰ
    open UniversalElementᴰNotation _ _ termᴰ
    open Terminal'Notation term'

    𝟙ᴰ : Cᴰ.ob[ 𝟙 ]
    𝟙ᴰ = termᴰ .vertexᴰ

    !tᴰ : ∀ {c} (d : Cᴰ.ob[ c ]) → Cᴰ.Hom[ !t ][ d , 𝟙ᴰ ]
    !tᴰ {c} d = introᴰ tt tt

    𝟙ηᴰ : ∀ {c} {d : Cᴰ.ob[ c ]} {f} (fᴰ : Cᴰ.Hom[ f ][ d , 𝟙ᴰ ])
        → fᴰ Cᴰ.≡[ η ] !tᴰ d
    𝟙ηᴰ {c} {d} {f} fᴰ = ηᴰ

  module _ (c : C .ob) where
    -- Vertical terminal object over a fixed object

    -- If Cᴰ is a fibration, this is equivalent to a terminal object
    -- in the fiber over c that is preserved by reindexing
    TerminalⱽSpec : Presheafⱽ Cᴰ c ℓ-zero
    TerminalⱽSpec = TerminalPresheafᴰ _

    -- This says that for every morphism f : c' → c in C and
    -- d ∈ Cᴰ.ob[ c' ] there is a unique lift to fᴰ : Cᴰ [ f ][ d' , 1c ]
    -- In program logic terms this is the "trivial postcondition"
    Terminalⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    Terminalⱽ =
      UniversalElementⱽ Cᴰ c TerminalⱽSpec

    module TerminalⱽNotation (vt : Terminalⱽ) where
      open UniversalElementⱽ vt public
      𝟙ⱽ : Cᴰ.ob[ c ]
      𝟙ⱽ = vertexⱽ

      !tⱽ : ∀ {c'}(f : C [ c' , c ]) (d' : Cᴰ.ob[ c' ]) → Cᴰ [ f ][ d' , 𝟙ⱽ ]
      !tⱽ f d' = introⱽ f tt

  hasAllTerminalⱽ : Type _
  hasAllTerminalⱽ = ∀ c → Terminalⱽ c

  module _ {term : Terminal' C} where
    open Terminal'Notation term
    open UniversalElementᴰ
    open UniversalElement
    open UniversalElementⱽ
    private module R = HomᴰReasoning Cᴰ


    Terminalⱽ→Terminalᴰ : Terminalⱽ 𝟙 → Terminalᴰ term
    Terminalⱽ→Terminalᴰ termⱽ .vertexᴰ = termⱽ .vertexⱽ
    Terminalⱽ→Terminalᴰ termⱽ .elementᴰ = tt
    Terminalⱽ→Terminalᴰ termⱽ .universalᴰ .inv _ = termⱽ .universalⱽ .fst
    Terminalⱽ→Terminalᴰ termⱽ .universalᴰ .rightInv _ _ = refl
    Terminalⱽ→Terminalᴰ termⱽ .universalᴰ .leftInv f fᴰ = R.rectify $ R.≡out $
      (R.≡in $ λ i → TerminalⱽNotation.!tⱽ _ termⱽ (𝟙η f (~ i)) _)
      ∙ (sym $ R.≡in $ ηⱽ termⱽ )
