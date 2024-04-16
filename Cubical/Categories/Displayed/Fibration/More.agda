{-# OPTIONS --safe #-}
module Cubical.Categories.Displayed.Fibration.More where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Fibration
open import Cubical.Categories.Displayed.Adjoint.More

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} where
  module _ {isFibCᴰ : isFibration Cᴰ} {isFibDᴰ : isFibration Dᴰ} where
    open import Cubical.Categories.Functor
    open import Cubical.Categories.Displayed.Functor
    module _ {F : Functor C D} {Fᴰ : Functorᴰ F Cᴰ Dᴰ} where
      open import Cubical.Categories.Displayed.Functor
      open Functorᴰ
      module Cᴰ = Categoryᴰ Cᴰ
      -- whether a 1-cell preserves morphisms
      isFibration' : Type _
      isFibration' =
        ∀ {c c' : C .ob} (c'ᴰ : Cᴰ.ob[ c' ]) (f : C [ c , c' ]) →
        (f*c'ᴰ : Cᴰ.ob[ c ])(fᴰ : Cᴰ.Hom[ f ][ f*c'ᴰ , c'ᴰ ]) →
          isCartesianOver Cᴰ c'ᴰ f ( f*c'ᴰ , fᴰ ) → isCartesianOver Dᴰ (Fᴰ .F-obᴰ c'ᴰ) (F ⟪ f ⟫) (Fᴰ .F-obᴰ f*c'ᴰ , Fᴰ .F-homᴰ fᴰ)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{fib : isFibration Cᴰ} where
-- 1-cell of fibrations
  open import Cubical.Categories.Displayed.Instances.Terminal
  TerminalFib : Categoryᴰ C _ _
  TerminalFib = Unitᴰ C
  open import Cubical.Data.Unit
  isFibTerminal : isFibration TerminalFib
  isFibTerminal dᴰ = CartesianOver→CartesianLift TerminalFib
    (record { f*cᴰ' = _ ; π = _ ; isCartesian = λ _ _ _ → uniqueExists _ (isPropUnit _ _) (λ _ _ _ → isSetUnit _ _ _ _) λ _ _ → isPropUnit _ _ })
  -- ! into TerminalFib
  open import Cubical.Categories.Functor.Base
  open import Cubical.Categories.Displayed.Functor
  TerminalFib! : Functorᴰ Id Cᴰ TerminalFib
  TerminalFib! .Functorᴰ.F-obᴰ = λ _ → tt
  TerminalFib! .Functorᴰ.F-homᴰ = λ _ → tt
  TerminalFib! .Functorᴰ.F-idᴰ = refl
  TerminalFib! .Functorᴰ.F-seqᴰ = λ fᴰ gᴰ → {!!}
  --isFibration'
  -- Jacobs 1.8.8
  -- Hermida 1.4.1
  hasFibTerminal : Type _
  hasFibTerminal = LocalRightAdjointᴰ {!!}
