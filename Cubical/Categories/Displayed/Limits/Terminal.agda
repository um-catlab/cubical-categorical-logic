-- There are two "obvious" ways to generalize limits to displayed
-- categories.
--
-- 1. The "displayed limit": the total category has the limit, and
-- first projection strictly preserves it.
--
-- 2. The "vertical limit": each fiber category has the limit, and the
-- displayed morphism profunctors preserve it. If the displayed
-- category is a fibration, then reindexing will preserve the limit,
-- but the definition makes sense even if you aren't working with a
-- fibration.
--
-- In the presence of enough fibration structure, vertical implies
-- displayed.
--
-- For terminal objects these look like the following:
--
-- 1. A displayed terminal object is an object over a terminal object
-- in the base such that there is a unique displayed morphism into it.
--
-- 2. A vertical terminal object over c is an object over c such that
-- there is a unique displayed morphism into it.
--
-- In this case, we can construct a displayed terminal object over any
-- terminal object in the base from a vertical terminal object over it
-- without any additional fibration structure.
module Cubical.Categories.Displayed.Limits.Terminal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.TotalCategory as ∫
open import Cubical.Categories.Limits.Terminal.More hiding (preservesTerminal)
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.Reasoning as HomᴰReasoning
open import Cubical.Categories.Displayed.Presheaf.Constructions.Unit
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.Presheaf.Section
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓP ℓQ : Level

open Category
open Categoryᴰ
open Functorᴰ
open isIsoOver

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  -- Terminal object over a terminal object
  Terminalᴰ : (term : Terminal' C) →
    Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
  Terminalᴰ term = UniversalElementᴰ Cᴰ term UnitPshᴰ

  module TerminalᴰNotation {term' : Terminal' C}
    (termᴰ : Terminalᴰ term') where

    open UniversalElement
    open UniversalElementNotation term'
    open UniversalElementᴰ termᴰ
    open TerminalNotation term'

    module 𝟙ueᴰ = UniversalElementᴰ termᴰ

    𝟙ᴰ : Cᴰ.ob[ 𝟙 ]
    𝟙ᴰ = vertexᴰ

    !tᴰ : ∀ {c} (d : Cᴰ.ob[ c ]) → Cᴰ.Hom[ !t ][ d , 𝟙ᴰ ]
    !tᴰ {c} d = introᴰ tt

    ∫term : Terminal' (∫C Cᴰ)
    ∫term .vertex = ∫ue.vertex
    ∫term .element = tt
    ∫term .universal (c , cᴰ) = isIsoToIsEquiv
      ( (λ _ → !t , !tᴰ cᴰ)
      , (λ _ → refl)
      , λ _ → sym $ ∫ue.η)

    𝟙extensionalityᴰ : ∀ {cc'} {f g : (∫C Cᴰ) [ cc' , (𝟙 , 𝟙ᴰ) ]} → f ≡ g
    𝟙extensionalityᴰ = UniversalElementNotation.extensionality ∫term refl

  module _ (c : C .ob) where
    -- Vertical terminal object over a fixed object

    -- This says that for every morphism f : c' → c in C and
    -- d ∈ Cᴰ.ob[ c' ] there is a unique lift to fᴰ : Cᴰ [ f ][ d' , 1c ]
    -- In program logic terms this is the "trivial postcondition"
    Terminalⱽ : Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓCᴰ) ℓCᴰ')
    Terminalⱽ = UniversalElementⱽ Cᴰ c UnitPshᴰ

    module TerminalⱽNotation (vt : Terminalⱽ) where
      open UniversalElementⱽ vt public
      𝟙ⱽ : Cᴰ.ob[ c ]
      𝟙ⱽ = vertexⱽ

      !tⱽ : ∀ {c'}(f : C [ c' , c ]) (d' : Cᴰ.ob[ c' ]) → Cᴰ [ f ][ d' , 𝟙ⱽ ]
      !tⱽ f d' = introᴰ tt

  Terminalsⱽ : Type _
  Terminalsⱽ = ∀ c → Terminalⱽ c

  module _ {term : Terminal' C} where
    open TerminalNotation term
    open UniversalElement
    open UniversalElementᴰ
    private module R = HomᴰReasoning Cᴰ
    module _ (termⱽ : Terminalⱽ 𝟙) where
      private module termⱽ = TerminalⱽNotation _ termⱽ
      Terminalⱽ→Terminalᴰ : Terminalᴰ term
      Terminalⱽ→Terminalᴰ = termⱽ ◁PshIsoⱽᴰ UnitPshᴰ≅UnitPshᴰ
      private
        -- manual proof for comparison
        Terminalⱽ→Terminalᴰ' : Terminalᴰ term
        Terminalⱽ→Terminalᴰ' .vertexᴰ = termⱽ.vertexⱽ
        Terminalⱽ→Terminalᴰ' .elementᴰ = tt
        Terminalⱽ→Terminalᴰ' .universalᴰ .inv _ _ = termⱽ.!tⱽ _ _
        Terminalⱽ→Terminalᴰ' .universalᴰ .rightInv _ _ = refl
        Terminalⱽ→Terminalᴰ' .universalᴰ .leftInv _ _ = R.rectify $ R.≡out $
          termⱽ.∫ue.extensionality (ΣPathP (𝟙extensionality , refl))
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} (Fᴰ : GlobalSection Cᴰ) (term : Terminal' C) where
  private
    module Cᴰ = Categoryᴰ Cᴰ
  strictlyPreservesTerminal : Terminalᴰ Cᴰ term → Type _
  strictlyPreservesTerminal = strictlyPreservesUE Fᴰ (UnitPsh→UnitPshᴰ Fᴰ) term

  preservesTerminal : Type _
  preservesTerminal = preservesUE {Pᴰ = UnitPshᴰ {P = UnitPsh {C = C}}} Fᴰ (UnitPsh→UnitPshᴰ Fᴰ) term
