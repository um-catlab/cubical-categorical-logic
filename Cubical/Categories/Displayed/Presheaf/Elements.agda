{-# OPTIONS --safe #-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Elements where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Foundations.Equiv

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Terminal.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
import Cubical.Categories.Displayed.Reasoning as Reasoning
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf

open Category
open Categoryᴰ
open Functor
open UniversalElement
open UniversalElementᴰ

private
  variable
    ℓC ℓC' ℓS : Level

module _
  {C : Category ℓC ℓC'}
  (P : Presheaf C ℓS)
  where
  Elementsᴰ : Categoryᴰ C ℓS ℓS
  Elementsᴰ .ob[_] c = ⟨ P ⟅ c ⟆ ⟩
  Elementsᴰ .Hom[_][_,_] f ϕ ψ = ψ ∘ᴾ⟨ C , P ⟩ f ≡ ϕ
  Elementsᴰ .idᴰ = funExt⁻ (P .F-id) _
  Elementsᴰ ._⋆ᴰ_ p q = (congS (λ x → x _) (P .F-seq _ _) ∙ congS _ q) ∙ p
  Elementsᴰ .⋆IdLᴰ _ = isSet→isSet' ((P ⟅ _ ⟆) .snd) _ _ _ _
  Elementsᴰ .⋆IdRᴰ _ = isSet→isSet' ((P ⟅ _ ⟆) .snd) _ _ _ _
  Elementsᴰ .⋆Assocᴰ _ _ _ = isSet→isSet' ((P ⟅ _ ⟆) .snd) _ _ _ _
  Elementsᴰ .isSetHomᴰ = isSet→isGroupoid ((P ⟅ _ ⟆) .snd) _ _

  hasPropHomsElementsᴰ : hasPropHoms Elementsᴰ
  hasPropHomsElementsᴰ _ _ _ = (P ⟅ _ ⟆) .snd _ _

  module Elementsᴰ = Categoryᴰ Elementsᴰ
  UE : Type _
  UE = Terminal (∫C Elementsᴰ)
  test : UE → UniversalElement C P
  test ue .vertex = ue .fst .fst
  test ue .element = ue .fst .snd
  test ue .universal _ .equiv-proof _ = uniqueExists
    (ue .snd _ .fst .fst )
    (ue .snd _ .fst .snd)
    (λ _ → hasPropHomsElementsᴰ _ _ _)
    λ f p → congS fst (ue .snd _ .snd (f , p))
  --module _ (ue : UniversalElement C P) where
  --  ueᴰ : Σ[ c ∈ C .ob ] VerticalTerminalAt Elementsᴰ c
  --  ueᴰ .fst = ue .vertex
  --  ueᴰ .snd .vertexᴰ = ue .element
  --  ueᴰ .snd .elementᴰ = _
  --  ueᴰ .snd .universalᴰ .equiv-proof _ = ({!ue .universal _ .equiv-proof _!} , {!!}) , {!!}
