module Cubical.Categories.Limits.Terminal.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable


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

TerminalPresheaf : ∀ {C : Category ℓc ℓc'} → Presheaf C ℓ-zero
TerminalPresheaf = Constant _ _ (Unit , isSetUnit)

Terminal' :  ∀ (C : Category ℓc ℓc') → Type (ℓ-max ℓc ℓc')
Terminal' C = UniversalElement C (TerminalPresheaf {C = C})

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
