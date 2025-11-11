module Cubical.Categories.LocallySmall.Displayed.Constructions.Total where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Categories.LocallySmall.Category.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
open import Cubical.Categories.LocallySmall.Displayed.Category.Small
open import Cubical.Categories.LocallySmall.Variables

open Category
open Categoryᴰ
open Σω
open Liftω

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

    module ∫CᴰNotation where
      vᴰ[_] : (c : Cob) → Categoryᴰ Cᴰ.v[ c ] (λ cᴰ → Cobᴰᴰ (c , cᴰ)) _
      vᴰ[ c ] .Hom[_][_,_] fᴰ xᴰ yᴰ = Cᴰᴰ.Hom[ (id C , fᴰ) ][ xᴰ , yᴰ ]
      vᴰ[ c ] .idᴰ = Cᴰᴰ.idᴰ
      vᴰ[ c ] ._⋆ᴰ_ fᴰ gᴰ = Cᴰᴰ.reind (Cᴰ.reind-filler _ _) $ (fᴰ Cᴰᴰ.⋆ᴰ gᴰ)
      vᴰ[ c ] .⋆IdLᴰ fᴰ =
        ΣPathP (
          (Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⋆IdLᴰ _) ,
          (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
            (sym $ Cᴰᴰ.reind-filler _ _)
            ∙ Cᴰᴰ.⋆IdLᴰ _))
      vᴰ[ c ] .⋆IdRᴰ fᴰ =
        ΣPathP (
          (Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⋆IdRᴰ _) ,
          (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
            (sym $ Cᴰᴰ.reind-filler _ _)
            ∙ Cᴰᴰ.⋆IdRᴰ _))
      vᴰ[ c ] .⋆Assocᴰ fᴰ gᴰ hᴰ =
        ΣPathP (
          (Cᴰ.rectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler _ _)
            ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
            ∙ Cᴰ.⋆Assocᴰ _ _ _
            ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
            ∙ Cᴰ.reind-filler _ _
            ),
          (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $
            (sym $ Cᴰᴰ.reind-filler _ _)
            ∙ Cᴰᴰ.⟨ sym $ Cᴰᴰ.reind-filler _ _ ⟩⋆⟨⟩
            ∙ Cᴰᴰ.⋆Assocᴰ _ _ _
            ∙ Cᴰᴰ.⟨⟩⋆⟨ Cᴰᴰ.reind-filler _ _ ⟩
            ∙ Cᴰᴰ.reind-filler _ _
            ))
      vᴰ[ c ] .isSetHomᴰ = Cᴰᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}
  {Cᴰ-ℓ}{Cobᴰ}{CHom-ℓᴰ}
  (Cᴰ : SmallFibersCategoryᴰ C Cᴰ-ℓ Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
  module _
    -- The levels of Cᴰᴰ only depend on the
    -- base objects in C
    {C-ℓᴰᴰ : Cob → Level}
    {Cobᴰᴰ}
    {CHom-ℓᴰᴰ : Cob → Cob → Level}
    (Cᴰᴰ :
      SmallFibersCategoryᴰ Cᴰ.∫C
        (λ x → C-ℓᴰᴰ (x .fst))
        Cobᴰᴰ (λ x y → CHom-ℓᴰᴰ (x .fst) (y .fst)))
    where
    private
      module Cᴰᴰ = Categoryᴰ Cᴰᴰ

    ∫CᴰSF :
      SmallFibersCategoryᴰ C _
        (λ (x : Cob) →
          Σ[ xᴰ ∈ Cobᴰ x ] Cobᴰᴰ (x , liftω xᴰ))
        _
    ∫CᴰSF .Hom[_][_,_] f xᴰxᴰᴰ yᴰyᴰᴰ =
      Σ[ fᴰ ∈
        Cᴰ.Hom[ f ][
          liftω (xᴰxᴰᴰ .lowerω .fst) ,
          liftω (yᴰyᴰᴰ .lowerω .fst) ] ]
        Cᴰᴰ.Hom[ f , fᴰ ][
          liftω (xᴰxᴰᴰ .lowerω .snd) ,
          liftω (yᴰyᴰᴰ .lowerω .snd) ]
    ∫CᴰSF .idᴰ = Cᴰ.idᴰ , Cᴰᴰ.idᴰ
    ∫CᴰSF ._⋆ᴰ_ fᴰ gᴰ =
      (fᴰ .fst Cᴰ.⋆ᴰ gᴰ .fst) ,
      (fᴰ .snd Cᴰᴰ.⋆ᴰ gᴰ .snd)
    ∫CᴰSF .⋆IdLᴰ ffᴰ =
      ΣPathP ((C.⋆IdL _) , (
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ (ffᴰ .fst)) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdLᴰ (ffᴰ .snd)))))
    ∫CᴰSF .⋆IdRᴰ ffᴰ =
      ΣPathP ((C.⋆IdR _) , (
      ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ (ffᴰ .fst)) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆IdRᴰ (ffᴰ .snd)))))
    ∫CᴰSF .⋆Assocᴰ ffᴰ ggᴰ hhᴰ =
      ΣPathP (C.⋆Assoc _ _ _ ,
      (ΣPathP ((Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assoc _ _ _) ,
      (Cᴰᴰ.rectify $ Cᴰᴰ.≡out $ Cᴰᴰ.⋆Assoc _ _ _))))
    ∫CᴰSF .isSetHomᴰ = isSetΣ Cᴰ.isSetHomᴰ (λ _ → Cᴰᴰ.isSetHomᴰ)

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ)
  where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ
  module _
    {C-ℓᴰᴰ} {Cobᴰᴰ} {CHom-ℓᴰᴰ}
    (Cᴰᴰ : SmallFibersCategoryᴰ Cᴰ.∫C C-ℓᴰᴰ Cobᴰᴰ CHom-ℓᴰᴰ)
    where
    private
      module Cᴰᴰ = ∫CᴰNotation Cᴰ Cᴰᴰ

    module ∫CᴰSFNotation where
      -- SmallFiberedness is preserved under partial application
      -- of arguments in the base
      vᴰ[_]SF : (c : Cob) →
        SmallFibersCategoryᴰ Cᴰ.v[ c ] _
          (λ cᴰ → Cobᴰᴰ (c , cᴰ))
          (λ x y → CHom-ℓᴰᴰ (c , x) (c , y))
      vᴰ[ c ]SF = Cᴰᴰ.vᴰ[ c ]
