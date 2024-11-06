{-

  Displayed category of elements of a presheaf. The classical category
  of elements of a presheaf is isomorphic to the total category of
  this displayed category.

-}
{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Instances.Element where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Terminal
open import Cubical.Categories.Instances.Terminal.More as Terminal
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable as Presheaf
  hiding (UniversalElement)
open import Cubical.Categories.Presheaf.More
  hiding (UniversalElementOn)
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Constructions.BinProduct
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.HLevels.More
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Constructions.Graph
open import Cubical.Categories.Displayed.Constructions.Reindex.Eq
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Constructions.PropertyOver.Displayed
open import Cubical.Categories.Displayed.Constructions.TotalCategory
open import Cubical.Categories.Displayed.Constructions.SimpleTotalCategoryL
open import Cubical.Categories.Constructions.TotalCategory hiding (Fst; Snd)
open import Cubical.Categories.Bifunctor.Redundant as Bif hiding (Fst; Snd)
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓS ℓR : Level

open Section
open Functor

module _ (C : Category ℓC ℓC') (ℓR : Level) where
  Element : Categoryᴰ (C ×C PresheafCategory C ℓR) _ _
  Element =
    Graph {C = C}{D = PresheafCategory C ℓR} (Profunctor→Relatoro* Id)

  hasPropHomsElement : hasPropHoms Element
  hasPropHomsElement = hasPropHomsGraph (Profunctor→Relatoro* Id)

  UniversalElementOn : Categoryᴰ (C ×C PresheafCategory C ℓR) _ _
  UniversalElementOn = PropertyOverᴰ Element
    λ { {c , P} elt → isUniversal C P c elt }

  hasPropHomsUniversalElementOn : hasPropHoms UniversalElementOn
  hasPropHomsUniversalElementOn =
    hasPropHomsPropertyOverᴰ Element _ hasPropHomsElement

  UniversalElement : Categoryᴰ (PresheafCategory C ℓR) _ _
  UniversalElement = ∫Cᴰsl {D = C} UniversalElementOn

  hasContrHomsUniversalElement : hasContrHoms UniversalElement
  hasContrHomsUniversalElement {P}{Q} α (x , η , ηUniv) (y , ε , εUniv) =
    uniqueExists
      (εue.intro ((α ⟦ x ⟧) η))
      (εue.β , tt)
      (λ f → isProp× (Q .F-ob _ .snd _ _) isPropUnit)
      λ { f (f◂α , tt ) → sym (εue.η ∙ cong εue.intro f◂α) }
    where
      εue : Presheaf.UniversalElement C Q
      εue = record { vertex = y ; element = ε ; universal = εUniv }
      module εue = UniversalElementNotation εue

module _ (C : Category ℓC ℓC') (P : Presheaf C ℓR) where
  private
    P' : C o-[ ℓR ]-* TerminalCategory {ℓ* = ℓ-zero}
    P' = Bif.Sym (CurriedToBifunctor (FunctorFromTerminal P))

    Element' : Categoryᴰ _ _ _
    Element' = Graph P'

    module EqR = EqReindex {C = C}{D = C ×C TerminalCategory} Element'
      (Id ,F Terminal.intro)
      Eq.refl
      (λ _ _ → Eq.refl)
  Elemento : Categoryᴰ C ℓR ℓR
  Elemento = EqR.reindex
  private
    module Elemento = Categoryᴰ Elemento
    test-ob : ∀ c → Elemento.ob[ c ] ≡ ⟨ P ⟅ c ⟆ ⟩
    test-ob c = refl

-- Covariant version
module _ (C : Category ℓC ℓC') (P : Functor C (SET ℓR)) where
  private
    -- relies on the defn equality TerminalCategory ^op = TerminalCategory 
    P' : TerminalCategory {ℓ* = ℓ-zero} o-[ ℓR ]-* C
    P' = CurriedToBifunctor (FunctorFromTerminal P)

    Element' : Categoryᴰ _ _ _
    Element' = Graph P'
    
    module EqR = EqReindex {C = C}{D = TerminalCategory ^op ×C C} Element'
      ((Terminal.intro ^opF) ,F Id)
      Eq.refl
      (λ _ _ → Eq.refl)

  Element∙ : Categoryᴰ C ℓR ℓR
  Element∙ = EqR.reindex
