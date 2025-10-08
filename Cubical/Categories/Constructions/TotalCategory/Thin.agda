module Cubical.Categories.Constructions.TotalCategory.Thin where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.ChangeOfHoms

open import Cubical.Categories.Displayed.Base

open import Cubical.Categories.Constructions.TotalCategory

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where

  open Category
  open Categoryᴰ Cᴰ
  private
    module C = Category C

  module _ (thin : ∀ (c d : C.ob) → isProp (C [ c , d ])) where
    ∫Cthin : Category {!!} {!!}
    ∫Cthin =
      ChangeOfHoms (∫C Cᴰ)
        (λ (c , cᴰ) (d , dᴰ) → {!!})
        {!!}
        {!!}


  module _ (thinᴰ : {!!}) where
