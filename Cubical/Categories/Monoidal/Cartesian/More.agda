{-
  Sketch: a `CartesianMonoidalCategory` record — a MonoidalCategory whose
  monoidal structure is the derived cartesian one. Bundles the raw
  cartesian data (BinProducts + Terminal, standard-cubical style) with the
  canonical derivation via `cartesianMonoidalStr`, and exposes both the
  underlying `MonoidalCategory` view and cartesian-side notation
  (`_×_`, `𝟙`, `π₁`, `π₂`, `⟨_,_⟩`, `!t`).
-}
module Cubical.Categories.Monoidal.Cartesian.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Monoidal.Cartesian using (cartesianMonoidalStr)
open import Cubical.Categories.Monoidal.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Limits.Terminal
  using (Terminal; isTerminal; terminalOb; terminalArrow)
open import Cubical.Categories.Limits.BinProduct
  using (BinProducts; module BinProducts)

private variable
  ℓ ℓ' ℓM ℓM' ℓN ℓN' : Level

-- A MonoidalCategory that is cartesian: its ⊗ *is* the categorical binary
-- product and its unit *is* the terminal.
record CartesianMonoidalCategory (ℓ ℓ' : Level)
  : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
  no-eta-equality
  field
    C    : Category ℓ ℓ'
    bp   : BinProducts C
    term : Terminal C

  asMonoidal : MonoidalCategory ℓ ℓ'
  asMonoidal .MonoidalCategory.C = C
  asMonoidal .MonoidalCategory.monstr = cartesianMonoidalStr C bp term

  open Category C public
  open BinProducts C bp public
    using (binProdArrowPr₁; binProdArrowPr₂; binProdArrowUnique;
           binProdArrowCompLeft; binProdArrowCompRight)
    renaming (binProdOb    to _×_
            ; binProdPr₁   to π₁
            ; binProdPr₂   to π₂
            ; binProdArrow to ⟨_,_⟩
            ; binProdMap   to _×ₕ_)
  𝟙 : ob
  𝟙 = terminalOb C term
  !t : ∀ {x} → Hom[ x , 𝟙 ]
  !t {x} = terminalArrow C term x

------------------------------------------------------------------------
-- Product-preservation for a lax monoidal functor between cartesian
-- monoidal categories.
module _
  (M : CartesianMonoidalCategory ℓM ℓM')
  (N : CartesianMonoidalCategory ℓN ℓN')
  where
  private
    module M = CartesianMonoidalCategory M
    module N = CartesianMonoidalCategory N

  record IsProductPreserving
    (F : LaxMonoidalFunctor M.asMonoidal N.asMonoidal)
    : Type (ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN'))
    where
    private
      module F = LaxMonoidalFunctor F
      Fob = LaxMonoidalFunctor.F F .Functor.F-ob
      Fhom : ∀ {x y} → M.C [ x , y ] → N.C [ Fob x , Fob y ]
      Fhom = LaxMonoidalFunctor.F F .Functor.F-hom
    field
      μ-isIso   : ∀ x y → isIso N.C F.μ⟨ x , y ⟩
      pres-π₁   : ∀ x y →
        F.μ⟨ x , y ⟩ N.⋆ Fhom (M.π₁ {x}{y}) ≡ N.π₁ {Fob x}{Fob y}
      pres-π₂   : ∀ x y →
        F.μ⟨ x , y ⟩ N.⋆ Fhom (M.π₂ {x}{y}) ≡ N.π₂ {Fob x}{Fob y}
      pres-unit : isTerminal N.C (Fob M.𝟙)

------------------------------------------------------------------------
-- Sketch: the `NatTrans-isMonoidal` theorem in Properties.agda would
-- take `CartesianMonoidalCategory` parameters directly:
--
--   module _
--     (M N     : CartesianMonoidalCategory _ _)
--     (F G     : LaxMonoidalFunctor M.asMonoidal N.asMonoidal)
--     (F-pres  : IsProductPreserving M N F)
--     (G-pres  : IsProductPreserving M N G)
--     (φ       : NatTrans (F.F) (G.F))
--     where
--     NatTrans-isMonoidal : MonoidalStr M.asMonoidal N.asMonoidal F G φ
--     ...  -- unchanged proof
--
-- And a concrete instance for presheaves would supply
--
--   𝓟MonCart : CartesianMonoidalCategory _ _
--   𝓟MonCart .C    = PRESHEAF A ℓm
--   𝓟MonCart .bp   = PSHBP-standard   -- converter from More.BinProducts
--   𝓟MonCart .term = PSH1-standard    -- converter from Terminal'
--
-- so that `𝓟MonCart .asMonoidal` is definitionally the presheaf
-- MonoidalCategory (replacing the ad-hoc `PshMon.𝓟Mon`).
