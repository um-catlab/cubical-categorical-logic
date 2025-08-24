{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.Cartesian where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Base
open import Cubical.Categories.Displayed.Limits.BinProduct.Properties
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
import Cubical.Categories.Displayed.Presheaf.CartesianLift as PshFib
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Presheaf

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

record CartesianCategoryᴰ (CC : CartesianCategory ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategory CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termᴰ : Terminalᴰ Cᴰ term
    bpᴰ   : BinProductsᴰ Cᴰ bp

  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
    cartesianLifts : isFibration Cᴰ

  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryⱽ' (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termⱽ : Terminalsⱽ Cᴰ
    bpⱽ   : BinProductsⱽ Cᴰ
  module Cᴰ = Categoryᴰ Cᴰ
  field
    cartesianLifts : PshFib.isCatFibration' Cᴰ

module _ {CC : CartesianCategory ℓC ℓC'}
         (CCᴰ : CartesianCategoryⱽ (CC .CartesianCategory.C) ℓCᴰ ℓCᴰ') where
  open CartesianCategory CC
  open TerminalNotation term
  open CartesianCategoryⱽ CCᴰ
  open CartesianCategoryᴰ hiding (Cᴰ)
  CartesianCategoryⱽ→CartesianCategoryᴰ : CartesianCategoryᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryᴰ .CartesianCategoryᴰ.Cᴰ = Cᴰ
  CartesianCategoryⱽ→CartesianCategoryᴰ .termᴰ = Terminalⱽ→Terminalᴰ Cᴰ (termⱽ 𝟙)
  CartesianCategoryⱽ→CartesianCategoryᴰ .bpᴰ =
    BinProductsⱽ→BinProductsᴰ Cᴰ cartesianLifts bpⱽ bp

record CartesianCategoryReprᴰ (CC : CartesianCategoryRepr ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  open CartesianCategoryRepr CC
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
    termᴰ : Representationᵁᴰ Cᴰ (TerminalPresheafᴰ* Cᴰ ℓCᴰ' (TerminalPresheaf* ℓC')) term
    bpᴰ   : ∀ {c} {d} cᴰ dᴰ
      → Representationᵁᴰ Cᴰ ((Cᴰ [-][-, cᴰ ]) ×ᴰPsh (Cᴰ [-][-, dᴰ ])) (bp c d)

  module Cᴰ = Categoryᴰ Cᴰ

record CartesianCategoryReprⱽ (C : Category ℓC ℓC') (ℓCᴰ ℓCᴰ' : Level)
  : Type (ℓ-suc (ℓ-max ℓC (ℓ-max ℓC' (ℓ-max ℓCᴰ ℓCᴰ')))) where
  no-eta-equality
  field
    Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'
  module Cᴰ = Categoryᴰ Cᴰ
  field
    termⱽ : ∀ {c} → Representationᵁⱽ Cᴰ (TerminalPresheafᴰ* Cᴰ ℓCᴰ' (C [-, c ]))
    bpⱽ   : ∀ {c} (cᴰ dᴰ : Cᴰ.ob[ c ]) → Representationᵁⱽ Cᴰ ((Cᴰ [-][-, cᴰ ]) ×ⱽPsh (Cᴰ [-][-, dᴰ ]))
    cartesianLifts : ∀ {c d} (f : C [ c , d ]) (dᴰ : Cᴰ.ob[ d ])
      → Representationᵁⱽ Cᴰ (reindYo f (Cᴰ [-][-, dᴰ ]))


module _ {CC : CartesianCategoryRepr ℓC ℓC'}
         (CCᴰ : CartesianCategoryReprⱽ (CC .CartesianCategoryRepr.C) ℓCᴰ ℓCᴰ') where
  open CartesianCategoryRepr CC
  open CartesianCategoryReprⱽ CCᴰ
  open CartesianCategoryReprᴰ hiding (Cᴰ)
  CartesianCategoryⱽ→CartesianCategoryReprᴰ : CartesianCategoryReprᴰ CC ℓCᴰ ℓCᴰ'
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .CartesianCategoryReprᴰ.Cᴰ = Cᴰ
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .termᴰ = _ ,
    (termⱽ .snd ∙ sym (reindTerminal* Cᴰ _)
    ◁ reindPathToPshIsoPathP (term .snd) _)
  CartesianCategoryⱽ→CartesianCategoryReprᴰ .bpᴰ cᴰ dᴰ =
    _ , ( bpⱽ _ _ .snd
        ◁ ×ᴰ≡π₁*×ⱽπ₂* (bp _ _) (cartesianLifts _ cᴰ) (cartesianLifts _ dᴰ))
