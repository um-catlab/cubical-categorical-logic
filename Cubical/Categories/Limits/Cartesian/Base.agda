{-# OPTIONS --safe #-}
module Cubical.Categories.Limits.Cartesian.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Categories.Category
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Data.Sigma hiding (_×_)

private
  variable
    ℓ ℓ' : Level

record CartesianCategory (ℓ ℓ' : Level) : Type (ℓ-max (ℓ-suc ℓ) (ℓ-suc ℓ')) where
  no-eta-equality
  field
    C : Category ℓ ℓ'
    term : Terminal' C
    bp   : BinProducts C

  -- potential performance issue
  open Category C
  open TerminalNotation term
  open BinProductsNotation bp

  unitor-l : ∀ {a} → CatIso C (𝟙 × a) a
  unitor-l .fst = π₂
  unitor-l .snd .isIso.inv = !t ,p id
  unitor-l .snd .isIso.sec = ×β₂
  unitor-l .snd .isIso.ret =
    π₂ ⋆ (!t ,p id)
      ≡⟨ ×ue.intro-natural _ _ ⟩
    ((π₂ ⋆ !t) ,p (π₂ ⋆ id))
      ≡⟨ ⟨ 𝟙extensionality ⟩,p⟨ ⋆IdR _ ⟩ ⟩
    (π₁ ,p π₂)
      ≡⟨ (sym $ ×ue.weak-η _ _) ⟩
    id
      ∎
