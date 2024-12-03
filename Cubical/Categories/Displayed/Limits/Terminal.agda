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
  LiftedTerminalSpec : Presheafᴰ Cᴰ (TerminalPresheaf {C = C}) ℓ-zero
  LiftedTerminalSpec = TerminalPresheafᴰ _

  LiftedTerminal : (term : Terminal' C) →
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  LiftedTerminal term = UniversalElementᴰ _ LiftedTerminalSpec term

  module LiftedTerminalNotation {term' : Terminal' C}
    (termᴰ : LiftedTerminal term') where

    open UniversalElement
    open UniversalElementᴰ
    open Terminal'Notation term'

    𝟙ᴰ : Cᴰ.ob[ 𝟙 ]
    𝟙ᴰ = termᴰ .vertexᴰ

    !tᴰ : ∀ {c} (d : Cᴰ.ob[ c ]) → Cᴰ.Hom[ !t ][ d , 𝟙ᴰ ]
    !tᴰ {c} d = termᴰ .universalᴰ !t .inv tt tt

    𝟙ηᴰ : ∀ {c} {d : Cᴰ.ob[ c ]} {f} (fᴰ : Cᴰ.Hom[ f ][ d , 𝟙ᴰ ])
        → fᴰ Cᴰ.≡[ 𝟙η f ] !tᴰ d
    𝟙ηᴰ {c} {d} {f} fᴰ = symP (termᴰ .universalᴰ !t .leftInv f fᴰ)

  module _ (c : C .ob) where
    -- Terminal object of the fiber of a fixed object

    -- TODO: Is this equivalent to the more "obvious" definition that
    -- Fiber c have a terminal object?
    -- No.
    VerticalTerminalSpec : VerticalPresheafᴰ Cᴰ c ℓ-zero
    VerticalTerminalSpec = TerminalPresheafᴰ _

    -- This says that for every morphism f : c' → c in C and
    -- d ∈ Cᴰ.ob[ c' ] there is a unique lift to fᴰ : Cᴰ [ f ][ d' , 1c ]
    -- In program logic terms this is the "trivial postcondition"
    VerticalTerminalAt : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    VerticalTerminalAt =
      UniversalElementᴰ Cᴰ VerticalTerminalSpec (selfUnivElt C c)

    module VerticalTerminalAtNotation (vt : VerticalTerminalAt) where
      open UniversalElementᴰ
      1ᴰ : Cᴰ.ob[ c ]
      1ᴰ = vt .vertexᴰ

      !tᴰ : ∀ {c'}(f : C [ c' , c ]) (d' : Cᴰ.ob[ c' ]) → Cᴰ [ f ][ d' , 1ᴰ ]
      !tᴰ f d' = vt .universalᴰ f .inv f tt

      -- !tᴰ-unique : ∀ {c'}(f : C [ c' , c ]) (d' : Cᴰ.ob[ c' ]) →
      --   isContr (Cᴰ [ f ][ d' , 1ᴰ ])
      -- !tᴰ-unique f d' .fst = !tᴰ f d'
      -- !tᴰ-unique f d' .snd fᴰ' = {!vt .universalᴰ .leftInv!}
        -- cong (λ p → p .fst) (vt .universalᴰ .equiv-proof tt .snd (fᴰ' , refl))

  VerticalTerminals : Type _
  VerticalTerminals = ∀ c → VerticalTerminalAt c

  module _ {term : Terminal' C} where
    open Terminal'Notation term
    open UniversalElementᴰ
    open UniversalElement
    private module R = HomᴰReasoning Cᴰ

    Vertical/𝟙→LiftedTerm : VerticalTerminalAt 𝟙 → LiftedTerminal term
    Vertical/𝟙→LiftedTerm vta .vertexᴰ = vta .vertexᴰ
    Vertical/𝟙→LiftedTerm vta .elementᴰ = vta .elementᴰ
    Vertical/𝟙→LiftedTerm vta .universalᴰ _ .inv _ _ =
      vta .universalᴰ !t .inv _ _
    Vertical/𝟙→LiftedTerm vta .universalᴰ _ .rightInv _ _ = refl
    Vertical/𝟙→LiftedTerm vta .universalᴰ x .leftInv  f fᴰ =
      R.rectify (R.≡out
        (ΣPathP (_ ,
          λ i → vta .universalᴰ !t .inv (𝟙η (f ⋆⟨ C ⟩ C .id) (~ i)) tt)
        ∙ ΣPathP (_ , vta .universalᴰ !t .leftInv f fᴰ)))

    AllVertical→Vertical/𝟙 : VerticalTerminals → LiftedTerminal term
    AllVertical→Vertical/𝟙 vtas = Vertical/𝟙→LiftedTerm (vtas _)
