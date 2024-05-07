{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
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
    ℓC ℓC' ℓD ℓD' ℓP : Level

open Category
open Categoryᴰ
open Functorᴰ

module _ {C : Category ℓC ℓC'} (D : Categoryᴰ C ℓD ℓD') where
  module D = Categoryᴰ D
  TerminalPresheafᴰ : (P : Presheaf C ℓP) → Presheafᴰ D P ℓ-zero
  TerminalPresheafᴰ P .F-obᴰ x x₁ = Unit , isSetUnit
  TerminalPresheafᴰ P .F-homᴰ = λ _ x _ → tt
  TerminalPresheafᴰ P .F-idᴰ i = λ x x₁ → tt
  TerminalPresheafᴰ P .F-seqᴰ fᴰ gᴰ i = λ x _ → tt

  -- Terminal object over a terminal object
  -- TODO: refactor using Constant Functorᴰ eventually
  TerminalᴰSpec : Presheafᴰ D (TerminalPresheaf {C = C}) ℓ-zero
  TerminalᴰSpec = TerminalPresheafᴰ _

  Terminalᴰ : (term : Terminal' C) → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
  Terminalᴰ term = UniversalElementᴰ _ TerminalᴰSpec term

  module _ {term' : Terminal' C} (termᴰ : Terminalᴰ term') where
    open UniversalElementᴰ
    open UniversalElement
    !t'ᴰ : ∀ {c} cᴰ → isContr (D.Hom[ !t' term' c .fst ][ cᴰ , termᴰ .vertexᴰ ])
    !t'ᴰ cᴰ .fst = invIsEq (termᴰ .universalᴰ) (termᴰ .elementᴰ)
    -- TODO: I've done this proof so many times just now
    -- where were all the other times? There's gotta be a lemma for this?
    !t'ᴰ cᴰ .snd fᴰ =
      congS (λ x → x .fst) (termᴰ .universalᴰ .equiv-proof tt .snd (fᴰ , refl))
    !ᴰ : {c : C .ob} (cᴰ : D.ob[ c ]) →
      ∃![ f ∈ (C [ c , term' .vertex ]) ] D.Hom[ f ][ cᴰ , termᴰ .vertexᴰ ]
    !ᴰ {c = c} cᴰ = uniqueExists
      (!t' term' c .fst)
      (!t'ᴰ cᴰ .fst)
      (λ f fᴰ fᴰ' → isContr→isProp
        (subst (λ x → isContr (D.Hom[ x ][ cᴰ , termᴰ .vertexᴰ ]))
        (!t' term' c .snd f) (!t'ᴰ cᴰ)) fᴰ fᴰ')
      λ f fᴰ → (!t' term' c .snd f)

  module _ (c : C .ob) where
    -- Terminal object of the fiber of a fixed object

    -- TODO: Is this equivalent to the more "obvious" definition that
    -- Fiber c have a terminal object?
    -- No.
    FibTerminalᴰSpec : Presheafᴰ D (C [-, c ]) ℓ-zero
    FibTerminalᴰSpec = TerminalPresheafᴰ (C [-, c ])

    -- This says that for every morphism f : c' → c in C and
    -- d' ∈ D.ob[ c' ] there is a unique lift to fᴰ : D [ f ][ d' , 1c ]
    -- In program logic terms this is the "trivial postcondition"
    FibTerminalᴰ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓD) ℓD')
    FibTerminalᴰ = UniversalElementᴰ D FibTerminalᴰSpec (selfUnivElt C c)

    module FibTerminalᴰNotation (fibTermᴰ : FibTerminalᴰ) where
      open UniversalElementᴰ
      1ᴰ : D.ob[ c ]
      1ᴰ = fibTermᴰ .vertexᴰ

      !tᴰ : ∀ {c'}(f : C [ c' , c ]) (d' : D.ob[ c' ]) → D [ f ][ d' , 1ᴰ ]
      !tᴰ f d' = invIsEq (fibTermᴰ .universalᴰ) tt

      !tᴰ-unique : ∀ {c'}(f : C [ c' , c ]) (d' : D.ob[ c' ]) → isContr (D [ f ][ d' , 1ᴰ ])
      !tᴰ-unique f d' = !tᴰ f d' ,
        (λ fᴰ' →
          cong (λ p → p .fst)
          (fibTermᴰ .universalᴰ .equiv-proof tt .snd (fᴰ' , refl)))
