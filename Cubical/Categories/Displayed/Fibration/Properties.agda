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
open import Cubical.Categories.Displayed.Adjoint.More

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

    -- Some relevant lemmas:
    -- Jacobs 1.8.8
    -- Hermida 1.4.1
    -- Hermida 3.3.3.i: VerticalRightAdjointᴰ s are automatically fibered?
    -- Hermida 3.3.6
    -- In Jacobs too

    -- possible alternative definition
    VerticalTerminalsᴰ' : Type _
    VerticalTerminalsᴰ' = VerticalRightAdjointᴰ (!ₚ .over)

-- This makes sense for any displayed category,
-- but is traditionally used for fibrations
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  VerticalTerminalsᴰ : Type _
  VerticalTerminalsᴰ = (c : C .ob) → VerticalTerminalAtᴰ Cᴰ c

  module _ (term : Terminal' C) where

    open VerticalTerminalAtᴰNotation Cᴰ
    open UniversalElementᴰ
    open UniversalElement
    private module Cᴰ = Categoryᴰ Cᴰ

    Verticalᴰ/𝟙 = VerticalTerminalAtᴰ Cᴰ (term .vertex)

    Verticalᴰ/𝟙→LiftedTermᴰ : Verticalᴰ/𝟙 → LiftedTerminalᴰ Cᴰ term
    Verticalᴰ/𝟙→LiftedTermᴰ 1ᴰ/1 .vertexᴰ = 1ᴰ/1 .vertexᴰ
    Verticalᴰ/𝟙→LiftedTermᴰ _ .elementᴰ = tt
    Verticalᴰ/𝟙→LiftedTermᴰ 1ᴰ/1 .universalᴰ  {xᴰ = xᴰ} {f = f} .equiv-proof _ =
      uniqueExists (!tᴰ (term .vertex) 1ᴰ/1 f xᴰ) refl
      (λ _ p q →
        LiftedTerminalᴰSpec Cᴰ .Functorᴰ.F-obᴰ xᴰ
        (TerminalPresheaf {C = C} .Functor.F-hom f (term .element))
          .snd tt tt p q)
        λ fᴰ' _ → !tᴰ-unique (term .vertex) 1ᴰ/1 f xᴰ .snd fᴰ'

    -- convenience
    AllVertical→Vertical/𝟙 : VerticalTerminalsᴰ → Verticalᴰ/𝟙
    AllVertical→Vertical/𝟙 vt = vt (term .vertex)

    -- convenience
    AllVertical→LiftedTermᴰ : VerticalTerminalsᴰ → LiftedTerminalᴰ Cᴰ term
    AllVertical→LiftedTermᴰ vt =
      Verticalᴰ/𝟙→LiftedTermᴰ (AllVertical→Vertical/𝟙 vt)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  (F : Functor C D)
  (Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ')
  (vt : VerticalTerminalsᴰ Dᴰ) where
  open UniversalElementᴰ
  open CartesianOver

  -- (this is not just an eta expansion)
  reind-VerticalTerminalsᴰ : VerticalTerminalsᴰ (reindex Dᴰ F)
  reind-VerticalTerminalsᴰ c .vertexᴰ = vt (F ⟅ c ⟆) .vertexᴰ
  reind-VerticalTerminalsᴰ c .elementᴰ = vt (F ⟅ c ⟆) .elementᴰ
  reind-VerticalTerminalsᴰ c .universalᴰ = vt (F ⟅ c ⟆) .universalᴰ

  module _ (term' : Terminal' C) where
    -- TODO: this name should be for the "end-to-end" function that reindexes
    -- the lifted structure of a fibration, by reindexing the vertical structure
    reind-LiftedTermᴰ : LiftedTerminalᴰ (reindex Dᴰ F) term'
    reind-LiftedTermᴰ = Verticalᴰ/𝟙→LiftedTermᴰ (reindex Dᴰ F) term'
      (AllVertical→Vertical/𝟙 (reindex Dᴰ F) term' reind-VerticalTerminalsᴰ)
