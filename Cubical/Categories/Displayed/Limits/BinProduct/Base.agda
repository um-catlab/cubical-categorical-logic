{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Limits.BinProduct.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma as Σ hiding (_×_)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Constructions.Fiber

open import Cubical.Categories.Displayed.Base
import Cubical.Categories.Displayed.BinProduct as BP
open import Cubical.Categories.Displayed.Bifunctor
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.FunctorComprehension
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.Constructions
open import Cubical.Categories.Displayed.Profunctor
open import Cubical.Categories.Displayed.Instances.Sets.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

open Category
open Bifunctorᴰ
open Functorᴰ

-- Displayed
module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓD ℓD') where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ

  -- TODO: if we make a redundant displayed product we could use it here
  BinProductᴰProf' :
    Bifunctorᴰ (BinProductProf' C) Cᴰ Cᴰ (PRESHEAFᴰ Cᴰ _ _)
  BinProductᴰProf' = compLRᴰ PshProdᴰ YOᴰ YOᴰ

  BinProductᴰ : ∀ {c12}
    → BinProduct C c12
    → (Cᴰ.ob[ c12 .fst ] Σ.× Cᴰ.ob[ c12 .snd ])
    → Type _
  BinProductᴰ bp (cᴰ₁ , cᴰ₂) =
    UniversalElementᴰ Cᴰ bp (BinProductᴰProf' .Bif-obᴰ cᴰ₁ cᴰ₂)

  BinProductsᴰ : BinProducts C → Type _
  BinProductsᴰ bp =
    ∀ {c12} (cᴰ12 : (Cᴰ.ob[ c12 .fst ] Σ.× Cᴰ.ob[ c12 .snd ]))
    → BinProductᴰ (bp c12) cᴰ12

  ProdWithAProfᴰ : ∀ {c} (cᴰ : Cᴰ.ob[ c ])
    → Profunctorᴰ (ProdWithAProf C c) Cᴰ Cᴰ _
  ProdWithAProfᴰ cᴰ = appRᴰ BinProductᴰProf' cᴰ

  BinProductsWithᴰ : ∀ {c}
    → BinProductsWith C c
    → Cᴰ.ob[ c ]
    → Type _
  BinProductsWithᴰ bp cᴰ = UniversalElementsᴰ bp (ProdWithAProfᴰ cᴰ)

  module _ {c} (-×c : BinProductsWith C c)
           {cᴰ} (-×ᴰcᴰ : BinProductsWithᴰ -×c cᴰ)
           where
    BinProductWithFᴰ : Functorᴰ (BinProductWithF C -×c) Cᴰ Cᴰ
    BinProductWithFᴰ =
      FunctorᴰComprehension (ProdWithAProfᴰ cᴰ) -×ᴰcᴰ

  -- Vertical Binary Products
  BinProductProfⱽ : Profunctorⱽ (Cᴰ BP.×ᴰ Cᴰ) Cᴰ ℓD'
  BinProductProfⱽ =
    PshProdⱽ ∘Fⱽᴰ ((YOᴰ ∘Fᴰⱽ Fstⱽ Cᴰ Cᴰ) ,Fⱽ (YOᴰ ∘Fᴰⱽ Sndⱽ Cᴰ Cᴰ))

  BinProductⱽ : ∀ {c} → (Cᴰ.ob[ c ] Σ.× Cᴰ.ob[ c ]) → Type _
  BinProductⱽ {c} (cᴰ₁ , cᴰ₂) =
    UniversalElementⱽ Cᴰ c (BinProductProfⱽ .F-obᴰ (cᴰ₁ , cᴰ₂))

  BinProductsⱽ : Type _
  BinProductsⱽ = UniversalElementsⱽ BinProductProfⱽ

  BinProductsWithⱽ : ∀ {c}
    → Cᴰ.ob[ c ]
    → Type _
  BinProductsWithⱽ {c} cᴰ = ∀ cᴰ' → BinProductⱽ (cᴰ' , cᴰ)

  module BinProductⱽNotation {c}{cᴰ cᴰ' : Cᴰ.ob[ c ]}
    (vbp : BinProductⱽ (cᴰ , cᴰ')) where

    open UniversalElementⱽ vbp public

    vert : Cᴰ.ob[ c ]
    vert = vertexⱽ

    -- shorthand for terminal vertical cone
    π₁₂ :
      Cᴰ.Hom[ C .id ][ vert , cᴰ ] Σ.× Cᴰ.Hom[ C .id ][ vert , cᴰ' ]
    π₁₂ = elementⱽ
    π₁ = π₁₂ .fst
    π₂ = π₁₂ .snd

    module _ {x : C .ob}{xᴰ : Cᴰ.ob[ x ]}{f : C [ x , c ]} where
      private
        module Cⱽ = Fibers Cᴰ
      infixr 4 _,ⱽ_
      _,ⱽ_ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ] →
        Cᴰ.Hom[ f ][ xᴰ , cᴰ' ] →
        Cᴰ.Hom[ f ][ xᴰ , vert ]
      (fᴰ ,ⱽ fᴰ') = introᴰ (fᴰ , fᴰ')

      opaque
        ,ⱽ≡ : ∀ {g}
          {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
          → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
          → {gᴰ : Cᴰ.Hom[ g ][ xᴰ , vert ]}
          → Path Cⱽ.Hom[ _ , _ ] (f , fᴰ) (g , gᴰ Cⱽ.⋆ᴰⱽ π₁)
          → Path Cⱽ.Hom[ _ , _ ] (f , fᴰ') (g , gᴰ Cⱽ.⋆ᴰⱽ π₂)
          → Path Cⱽ.Hom[ _ , _ ] (f , (fᴰ ,ⱽ fᴰ')) (g , gᴰ)
        ,ⱽ≡ fᴰ≡ fᴰ'≡ = ∫ue.intro≡ (ΣPathP (cong fst fᴰ≡ ∙ (sym $ C.⋆IdR _)
          , (ΣPathP
          ( (Cⱽ.rectify $ Cⱽ.≡out $ fᴰ≡ ∙ (sym $ Cⱽ.reind-filler _ _))
          , (Cⱽ.rectify $ Cⱽ.≡out $ fᴰ'≡ ∙ (sym $ Cⱽ.reind-filler _ _))))))

        ×βⱽ₁ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
           → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
           → (fᴰ ,ⱽ fᴰ') Cⱽ.⋆ᴰⱽ π₁ ≡ fᴰ
        ×βⱽ₁ = cong fst βⱽ

        ∫×βⱽ₁ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
           → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
           → Path Cⱽ.Hom[ _ , _ ]
               (f , (fᴰ ,ⱽ fᴰ') Cⱽ.⋆ᴰⱽ π₁) (f , fᴰ)
        ∫×βⱽ₁ = Cⱽ.≡in ×βⱽ₁

        ×βⱽ₂ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
          → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
         → (fᴰ ,ⱽ fᴰ') Cⱽ.⋆ᴰⱽ π₂ ≡ fᴰ'
        ×βⱽ₂ = cong snd βⱽ

        ∫×βⱽ₂ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , cᴰ ]}
           → {fᴰ' : Cᴰ.Hom[ f ][ xᴰ , cᴰ' ]}
           → Path Cⱽ.Hom[ _ , _ ]
               (f , (fᴰ ,ⱽ fᴰ') Cⱽ.⋆ᴰⱽ π₂) (f , fᴰ')
        ∫×βⱽ₂ = Cⱽ.≡in ×βⱽ₂

        ×ηⱽ : {fᴰ : Cᴰ.Hom[ f ][ xᴰ , vert ]}
          → fᴰ ≡ (fᴰ Cⱽ.⋆ᴰⱽ π₁ ,ⱽ fᴰ Cⱽ.⋆ᴰⱽ  π₂)
        ×ηⱽ = ηⱽ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓD ℓD'} where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ

  module BinProductᴰNotation {c d} {cᴰ : Cᴰ.ob[ c ]}{dᴰ : Cᴰ.ob[ d ]}
    {bp : BinProduct C (c , d)}
    (bpᴰ : BinProductᴰ Cᴰ bp (cᴰ , dᴰ))
    where
    module ×ueᴰ = UniversalElementᴰ bpᴰ
    open ×ueᴰ
    open BinProductNotation bp

    π₁ᴰ = elementᴰ .fst
    π₂ᴰ = elementᴰ .snd
    _,pᴰ_ : ∀ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}
      {f₁ f₂}
      (f₁ᴰ : Cᴰ [ f₁ ][ Γᴰ , cᴰ ])
      (f₂ᴰ : Cᴰ [ f₂ ][ Γᴰ , dᴰ ])
      → Cᴰ [ f₁ ,p f₂ ][ Γᴰ , vertexᴰ ]
    f₁ᴰ ,pᴰ f₂ᴰ = introᴰ (f₁ᴰ , f₂ᴰ)

    module _ {Γ}{Γᴰ : Cᴰ.ob[ Γ ]}
      {f₁ f₂}
      {f₁ᴰ : Cᴰ [ f₁ ][ Γᴰ , cᴰ ]}
      {f₂ᴰ : Cᴰ [ f₂ ][ Γᴰ , dᴰ ]}
      where
      private
        ×βᴰ = ×ueᴰ.βᴰ {p = _ , f₁ᴰ , f₂ᴰ}

      ×βᴰ₁ : Path Cᴰ.Hom[ _ , _ ] (_ , (f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₁ᴰ) (_ , f₁ᴰ)
      ×βᴰ₁ i .fst = ×βᴰ i .fst .fst
      ×βᴰ₁ i .snd = ×βᴰ i .snd .fst

      ×βᴰ₂ : Path Cᴰ.Hom[ _ , _ ] (_ , (f₁ᴰ ,pᴰ f₂ᴰ) Cᴰ.⋆ᴰ π₂ᴰ) (_ , f₂ᴰ)
      ×βᴰ₂ i .fst = ×βᴰ i .fst .snd
      ×βᴰ₂ i .snd = ×βᴰ i .snd .snd

  module BinProductsᴰNotation {bp : BinProducts C}(bpᴰ : BinProductsᴰ Cᴰ bp)
    where
    open BinProductsNotation bp
    _×ᴰ_ : ∀ {c d} → Cᴰ.ob[ c ] → Cᴰ.ob[ d ] → Cᴰ.ob[ c × d ]
    cᴰ ×ᴰ dᴰ = UniversalElementᴰ.vertexᴰ (bpᴰ (cᴰ , dᴰ))

    module _ {c d}{cᴰ : Cᴰ.ob[ c ]}{dᴰ : Cᴰ.ob[ d ]} where
      open BinProductᴰNotation (bpᴰ (cᴰ , dᴰ)) hiding (module ×ueᴰ) public
    module ×ueᴰ {c d}(cᴰ : Cᴰ.ob[ c ])(dᴰ : Cᴰ.ob[ d ]) =
      BinProductᴰNotation.×ueᴰ (bpᴰ (cᴰ , dᴰ))
