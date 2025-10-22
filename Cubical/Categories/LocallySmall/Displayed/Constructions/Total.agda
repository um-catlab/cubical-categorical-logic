module Cubical.Categories.LocallySmall.Displayed.Constructions.Total where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

import Cubical.Categories.Category as Small
open import Cubical.Categories.LocallySmall.Base
open import Cubical.Categories.LocallySmall.Displayed.Base
open import Cubical.Categories.LocallySmall.Variables

open Category
open Categoryᴰ
open Σω

module _ {C : Category Cob CHom-ℓ}(Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
  module _ {Cobᴰᴰ CHom-ℓᴰᴰ}(Cᴰᴰ : Categoryᴰ Cᴰ.∫C Cobᴰᴰ CHom-ℓᴰᴰ) where
    private
      module Cᴰᴰ = Categoryᴰ Cᴰᴰ
    ∫Cᴰ : Categoryᴰ C (λ x → Σω[ xᴰ ∈ Cobᴰ x ] Cobᴰᴰ (x , xᴰ)) _
    ∫Cᴰ .Hom[_][_,_] f xᴰxᴰᴰ yᴰyᴰᴰ =
      Σ[ fᴰ ∈ Cᴰ.Hom[ f ][ xᴰxᴰᴰ .fst , yᴰyᴰᴰ .fst ] ]
        Cᴰᴰ.Hom[ f , fᴰ ][ xᴰxᴰᴰ .snd , yᴰyᴰᴰ .snd ]
    ∫Cᴰ .idᴰ = Cᴰ.idᴰ , Cᴰᴰ.idᴰ
    ∫Cᴰ ._⋆ᴰ_ ffᴰ ggᴰ = (ffᴰ .fst Cᴰ.⋆ᴰ ggᴰ .fst) , (ffᴰ .snd Cᴰᴰ.⋆ᴰ ggᴰ .snd)
    ∫Cᴰ .⋆IdLᴰ ffᴰ =
      ΣPathP ((C.⋆IdL _) , (
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ (ffᴰ .fst)) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdLᴰ (ffᴰ .snd)))))
    ∫Cᴰ .⋆IdRᴰ ffᴰ =
      ΣPathP ((C.⋆IdR _) , (
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ (ffᴰ .fst)) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdRᴰ (ffᴰ .snd)))))
    ∫Cᴰ .⋆Assocᴰ ffᴰ ggᴰ hhᴰ =
      ΣPathP (C.⋆Assoc _ _ _ ,
      (ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assoc _ _ _) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆Assoc _ _ _))))
    ∫Cᴰ .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)
