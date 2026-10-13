module Cubical.Categories.Limits.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt

private
  variable
    ℓ ℓ' ℓc ℓc' ℓd ℓd' : Level

preservesTerminal : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                  → Functor C D
                  → Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓd) ℓd')
preservesTerminal C D F = ∀ (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)


preserveOnePreservesAll : ∀ (C : Category ℓc ℓc')(D : Category ℓd ℓd')
                        → (F : Functor C D)
                        → (One : Terminal C) → isTerminal D (F ⟅ One .fst ⟆)
                        → preservesTerminal C D F
preserveOnePreservesAll C D F One D-preserves-One One' =
  isoToTerminal D
                ((F ⟅ One .fst ⟆) , D-preserves-One) (F ⟅ One' .fst ⟆)
                (F-Iso {F = F} (terminalToIso C One One'))

Terminal' :  ∀ (C : Category ℓc ℓc') → Type (ℓ-max ℓc ℓc')
Terminal' C = UniversalElement C UnitPsh

preservesTerminal' : ∀ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
                  → Functor C D
                  → (One : Terminal' C) → Type _
preservesTerminal' F term =
  preservesUniversalElement {F = F}{Q = UnitPsh}
    (invPshIso (reindPsh-Unit F) .PshIso.trans)
    term

terminalToUniversalElement : ∀ {C : Category ℓc ℓc'} (One : Terminal C)
  → Terminal' C
terminalToUniversalElement One .UniversalElement.vertex = One .fst
terminalToUniversalElement One .UniversalElement.element = tt
terminalToUniversalElement {C = C} One .UniversalElement.universal x = isoToIsEquiv (iso
  (λ _ → tt)
  (λ _ → terminalArrow C One _)
  (λ b i → tt)
  λ a → terminalArrowUnique C {T = One} a)

Terminal'ToTerminal : ∀ {C : Category ℓc ℓc'} → Terminal' C → Terminal C
Terminal'ToTerminal term' .fst = term' .UniversalElement.vertex
Terminal'ToTerminal term' .snd c =
  contr!t .fst .fst
  , (λ !t' → cong fst (contr!t .snd (!t' , refl)) )
  where contr!t = term' .UniversalElement.universal c .equiv-proof tt

module TerminalNotation {ℓ}{ℓ'} {C : Category ℓ ℓ'} (term' : Terminal' C) where
  module 𝟙ue = UniversalElementNotation term'
  private
    module C = Category C
  open 𝟙ue

  𝟙 : C.ob
  𝟙 = vertex

  !t : ∀ {a} → C [ a , 𝟙 ]
  !t = intro _

  𝟙extensionality : ∀ {a}{f g : C [ a , 𝟙 ]} → f ≡ g
  𝟙extensionality = extensionality refl

Initial' : ∀ (C : Category ℓc ℓc') → Type (ℓ-max ℓc ℓc')
Initial' C = Terminal' (C ^op)

module InitialNotation {ℓ}{ℓ'} {C : Category ℓ ℓ'} (init' : Initial' C) where
  open TerminalNotation init' public
    renaming (𝟙 to 𝟘; !t to absurd; 𝟙extensionality to 𝟘extensionality)
