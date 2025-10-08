module Cubical.Categories.Constructions.FullSubcategory.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Dependent

open import Cubical.Data.Unit
open import Cubical.Data.Sum

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Presheaf.Representable
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Constructions.PropertyOver
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Limits.BinProduct

private
  variable
    ℓC ℓC' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓS ℓR : Level

open Category
open Functor
open Categoryᴰ
open Functorᴰ
open UniversalElementᴰ
open isIsoOver

module _ (C : Category ℓC ℓC')
  where
  private
    module C = Category C
  open Category
  open Functor


  module FullSubcategory' (P : C.ob → Type ℓP) where
    Pᴰ = PropertyOver C P

    FullSubcategory' : Category (ℓ-max ℓC ℓP) (ℓ-max ℓC' ℓ-zero)
    FullSubcategory' = ∫C Pᴰ

    ι : Functor FullSubcategory' C
    ι = Fst {Cᴰ = Pᴰ}

    module _ (term : Terminal' C) where
      open TerminalNotation term
      module _ (P-term : P 𝟙) where
        termᴰ : Terminalᴰ Pᴰ term
        termᴰ .vertexᴰ = P-term
        termᴰ .elementᴰ = tt
        termᴰ .universalᴰ .inv _ _ = tt
        termᴰ .universalᴰ .rightInv _ _ = refl
        termᴰ .universalᴰ .leftInv _ _ = refl

        open TerminalᴰNotation _ termᴰ

        ∫termFull : Terminal' FullSubcategory'
        ∫termFull = ∫term

    module _ (init : Initial C) where
      open InitialNotation C init
      module _ (P-init : P 𝟘) where
        initᴰ : Initialᴰ Pᴰ init
        initᴰ .vertexᴰ = P-init
        initᴰ .elementᴰ = tt
        initᴰ .universalᴰ .inv _ _ = tt
        initᴰ .universalᴰ .rightInv _ _ = refl
        initᴰ .universalᴰ .leftInv _ _ = refl

        open InitialᴰNotation _ initᴰ

        ∫initFull : Initial FullSubcategory'
        ∫initFull = ∫init

    module _ (bp : BinProducts C) where
      open BinProductsNotation bp
      module _ (P-× : ∀ {c d} → P c → P d → P (c × d)) where
        bpᴰ : BinProductsᴰ Pᴰ bp
        bpᴰ cᴰ .vertexᴰ = P-× (cᴰ .fst) (cᴰ .snd)
        bpᴰ cᴰ .elementᴰ = tt , tt
        bpᴰ cᴰ .universalᴰ .inv _ _ = tt
        bpᴰ cᴰ .universalᴰ .rightInv _ _ = refl
        bpᴰ cᴰ .universalᴰ .leftInv _ _ = refl

        open BinProductsᴰNotation bpᴰ

        ∫bpFull : BinProducts FullSubcategory'
        ∫bpFull = ∫bp

    module _ (bcp : BinCoproducts C) where
      open BinCoproductsNotation bcp
      module _ (P-+ : ∀ {c d} → P c → P d → P (c + d)) where
        bcpᴰ : BinCoproductsᴰ Pᴰ bcp
        bcpᴰ cᴰ .vertexᴰ = P-+ (cᴰ .fst) (cᴰ .snd)
        bcpᴰ cᴰ .elementᴰ = tt , tt
        bcpᴰ cᴰ .universalᴰ .inv _ _ = tt
        bcpᴰ cᴰ .universalᴰ .rightInv _ _ = refl
        bcpᴰ cᴰ .universalᴰ .leftInv _ _ = refl

        open BinCoproductsᴰNotation _ bcpᴰ

        ∫bcpFull : BinCoproducts FullSubcategory'
        ∫bcpFull = ∫bcp
