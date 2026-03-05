module Cubical.Categories.LocallySmall.Instances.DisplayOverTerminal.Base where

open import Cubical.Foundations.Function


open import Cubical.Categories.LocallySmall.Variables
open import Cubical.Categories.LocallySmall.Category.Base
open import Cubical.Categories.LocallySmall.Instances.Unit

open import Cubical.Categories.LocallySmall.Displayed.Category.Base

open Category

module _ where
  open CategoryVariables
  module _
    (Cᴰ : Categoryᴰ UNIT Cobᴰ CHom-ℓᴰ) where
    private
      module Cᴰ = Categoryᴰ Cᴰ

    CatᴰOverUNIT→Cat : Category (Cobᴰ _) _
    CatᴰOverUNIT→Cat .Hom[_,_] = Cᴰ.Hom[ _ ][_,_]
    CatᴰOverUNIT→Cat .id = Cᴰ.idᴰ
    CatᴰOverUNIT→Cat ._⋆_ = Cᴰ._⋆ᴰ_
    CatᴰOverUNIT→Cat .⋆IdL _ = Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _
    CatᴰOverUNIT→Cat .⋆IdR _ = Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _
    CatᴰOverUNIT→Cat .⋆Assoc _ _ _ = Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _
    CatᴰOverUNIT→Cat .isSetHom = Cᴰ.isSetHomᴰ
