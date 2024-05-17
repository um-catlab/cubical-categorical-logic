{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Unit
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Terminal
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category


module _ {C : Category ℓC ℓC'} where
  open CartesianOver
  open FiberedFunctor

  isFibC/C : isFibration (Unitᴰ C)
  isFibC/C _ = CartesianOver→CartesianLift (Unitᴰ C) ue
    where
    ue : CartesianOver (Unitᴰ C) _ _
    ue .f*cᴰ' = tt
    ue .π = tt
    ue .isCartesian _ _ _ =
      uniqueExists _ (isPropUnit _ _) (λ _ → isSetUnit _ _)
      λ _ _ → isPropUnit _ _

  -- terminal fibration over C, ie the identity fibration
  TerminalFib : ClovenFibration C _ _
  TerminalFib = (Unitᴰ C , isFibC/C)

  module _ (p : ClovenFibration C ℓCᴰ ℓCᴰ') where
    open Functorᴰ

    !ₚ : FiberedFunctor p TerminalFib
    !ₚ .base = Id
    !ₚ .over .F-obᴰ _ = tt
    !ₚ .over .F-homᴰ _ = tt
    !ₚ .over .F-idᴰ = refl
    !ₚ .over .F-seqᴰ _ _ = refl
    !ₚ .preserves-cartesian _ _ _ _ _ _ _ _ =
        uniqueExists _ (isPropUnit _ _)
        (λ _ → isSetUnit _ _) λ _ _ → isPropUnit _ _

-- This makes sense for any displayed category, but is traditionally used for fibrations
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  AllVerticalTerminals : Type _
  AllVerticalTerminals = (c : C .ob) → VerticalTerminal Cᴰ c

  module _ (term : Terminal' C) where

    open VerticalTerminalNotation Cᴰ
    open UniversalElementᴰ
    open UniversalElement
    private module Cᴰ = Categoryᴰ Cᴰ

    Vertical/𝟙 = VerticalTerminal Cᴰ (term .vertex)

    Vertical/𝟙→LiftedTerm : Vertical/𝟙 → LiftedTerminal Cᴰ term
    Vertical/𝟙→LiftedTerm 1ᴰ/1 .vertexᴰ = 1ᴰ/1 .vertexᴰ
    Vertical/𝟙→LiftedTerm _ .elementᴰ = tt
    Vertical/𝟙→LiftedTerm 1ᴰ/1 .universalᴰ  {xᴰ = xᴰ} {f = f} .equiv-proof _ =
      uniqueExists (!tᴰ (term .vertex) 1ᴰ/1 f xᴰ) refl
      (λ _ p q →
        LiftedTerminalSpec Cᴰ .Functorᴰ.F-obᴰ xᴰ
        (TerminalPresheaf {C = C} .Functor.F-hom f (term .element)) .snd tt tt p q)
        λ fᴰ' _ → !tᴰ-unique (term .vertex) 1ᴰ/1 f xᴰ .snd fᴰ'

    -- convenience
    AllVertical→Vertical/𝟙 : AllVerticalTerminals → Vertical/𝟙
    AllVertical→Vertical/𝟙 vt = vt (term .vertex)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (vt : AllVerticalTerminals Dᴰ) where
  open UniversalElementᴰ
  -- (this is not just an eta expansion)
  reind-VerticalTerminal : AllVerticalTerminals (reindex Dᴰ F)
  reind-VerticalTerminal c .vertexᴰ = vt (F ⟅ c ⟆) .vertexᴰ
  reind-VerticalTerminal c .elementᴰ = vt (F ⟅ c ⟆) .elementᴰ
  reind-VerticalTerminal c .universalᴰ = vt (F ⟅ c ⟆) .universalᴰ
