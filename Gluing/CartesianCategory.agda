{-# OPTIONS --safe #-}
module Gluing.CartesianCategory where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Data.Nat
open import Cubical.Categories.Constructions.Free.CartesianCategory.Base
open import Cubical.Categories.Constructions.Free.CartesianCategory.ProductQuiver
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Properties as Disp
open import Cubical.Categories.Displayed.Instances.Sets

data OB : Type ℓ-zero where
  A B C : OB

-- using "hedberg's theorem"
-- NOTE to self: Zettel #13
isSetOB : isSet OB
isSetOB = Discrete→isSet
  (sectionDiscrete
  (λ { 0 → A ; 1 → B; _ → C })
  (λ { A → 0 ; B → 1 ; C → 2 })
  (λ { A → refl ; B → refl ; C → refl } )
  discreteℕ)

data MOR : Type ℓ-zero where
  f g : MOR

-- sim
isSetMOR : isSet MOR
isSetMOR = Discrete→isSet
  (sectionDiscrete
  (λ { 0 → f ; 1 → g ; _ → g })
  (λ { f → 0 ; g → 1 })
  (λ { f → refl ; g → refl })
  discreteℕ)

interleaved mutual -- not actually mutually recursive
  DOM COD : MOR → ProdExpr OB

  DOM f = ↑ A
  COD f = ↑ B

  DOM g = ↑ A
  COD g = ↑ C

QUIVER : ×Quiver
QUIVER .fst = OB
QUIVER .snd .ProductQuiver.mor = MOR
QUIVER .snd .ProductQuiver.dom = DOM
QUIVER .snd .ProductQuiver.cod = COD

open ×Quiver-Nice QUIVER

FREECC : CartesianCategory _ _
FREECC = FreeCartesianCategory QUIVER

open Category

|FREECC| : Category _ _
|FREECC| = FREECC .fst
FREECC-Cart : BinProducts |FREECC|
FREECC-Cart = FREECC .snd .snd

-- TODO
data NormalForm {Γ} : ∀{Δ} → |FREECC| [ Γ , Δ ] → Type (ℓ-suc ℓ-zero) where
  nil : NormalForm (|FREECC| .id)
  cons : ∀ gen
       → ∀{e}
       → NormalForm e
       → NormalForm (↑ₑ gen ∘⟨ |FREECC| ⟩ e)

forget : ∀{Γ Δ t} → NormalForm {Γ}{Δ} t → MOR -- or whatever
forget n = f -- TODO

-- TODO
normalize : ∀{Γ Δ} → (t : |FREECC| [ Γ , Δ ]) → NormalForm t
normalize {Γ} = {!!}
  where
  -- TODO: upgrade to cartesian
  pts : Functor |FREECC| (SET _)
  pts = |FREECC| [ Γ ,-] -- yoneda embedding of |FREECC| op?
  -- TODO: upgrade to displayed cartesian category
  LogFam : Categoryᴰ |FREECC| _ _
  LogFam = reindex (SETᴰ _ _) pts

-- our goal
private
  open Notation |FREECC| FREECC-Cart
  _ : forget (normalize (Exp.π₁ ∘⟨ |FREECC| ⟩ (↑ₑ f) ,p (↑ₑ g))) ≡ forget (normalize (↑ₑ f))
  _ = refl -- TODO
