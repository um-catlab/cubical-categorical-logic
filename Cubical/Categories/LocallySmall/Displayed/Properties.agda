module Cubical.Categories.LocallySmall.Displayed.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv.More

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
  record CatIsoᴰ {x y : Cob}(f : C.ISOC.Hom[ x , y ]) (xᴰ : Cobᴰ x ) (yᴰ : Cobᴰ y)
    : Type (ℓ-max (CHom-ℓ x x) $
            ℓ-max (CHom-ℓ x y) $
            ℓ-max (CHom-ℓ y x) $
            ℓ-max (CHom-ℓ y y) $
            ℓ-max (CHom-ℓᴰ x x xᴰ xᴰ) $
            ℓ-max (CHom-ℓᴰ x y xᴰ yᴰ) $
            ℓ-max (CHom-ℓᴰ y x yᴰ xᴰ) $
            ℓ-max (CHom-ℓᴰ y y yᴰ yᴰ) $
            ℓ-zero)
    where
    no-eta-equality
    constructor isoᴰ
    field
      funᴰ : Cᴰ.Hom[ f .CatIso.fun ][ xᴰ , yᴰ ]
      invᴰ : Cᴰ.Hom[ f .CatIso.inv ][ yᴰ , xᴰ ]
      secᴰ : Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
      retᴰ : Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ)

  CatIsoᴰIsoΣ : ∀ {x y}{f : C.ISOC.Hom[ x , y ]}{xᴰ yᴰ}
    → Iso (CatIsoᴰ f xᴰ yᴰ)
          (Σ[ funᴰ ∈ Cᴰ.Hom[ f .CatIso.fun ][ xᴰ , yᴰ ] ]
          Σ[ invᴰ ∈ Cᴰ.Hom[ f .CatIso.inv ][ yᴰ , xᴰ ] ]
          Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
          × Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ))
  unquoteDef CatIsoᴰIsoΣ = defineRecordIsoΣ CatIsoᴰIsoΣ (quote (CatIsoᴰ))

  ∫CatIso : {x y : Cob}{f : C.ISOC.Hom[ x , y ]} {xᴰ : Cobᴰ x}{yᴰ : Cobᴰ y}
    → (fᴰ : CatIsoᴰ f xᴰ yᴰ)
    → Cᴰ.ISOC.Hom[ (_ , xᴰ) , (_ , yᴰ) ]
  ∫CatIso fᴰ .CatIso.fun = _ , fᴰ .CatIsoᴰ.funᴰ
  ∫CatIso fᴰ .CatIso.inv = _ , fᴰ .CatIsoᴰ.invᴰ
  ∫CatIso fᴰ .CatIso.sec = fᴰ .CatIsoᴰ.secᴰ
  ∫CatIso fᴰ .CatIso.ret = fᴰ .CatIsoᴰ.retᴰ

  isIsoᴰ : ∀ {x y}{f : C.Hom[ x , y ]}(f⁻ : isIso C f)
    {xᴰ yᴰ}(funᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
    → Type _
  isIsoᴰ f⁻ funᴰ = Σ[ invᴰ ∈ Cᴰ.Hom[ f⁻ .fst ][ _ , _ ] ]
    Path Cᴰ.Hom[ _ , _ ] (_ , invᴰ Cᴰ.⋆ᴰ funᴰ) (_ , Cᴰ.idᴰ)
    × Path Cᴰ.Hom[ _ , _ ] (_ , funᴰ Cᴰ.⋆ᴰ invᴰ) (_ , Cᴰ.idᴰ)

  module _ {x y : Cob}{f g : C.ISOC.Hom[ x , y ]}
    {xᴰ yᴰ}{fᴰ : CatIsoᴰ f xᴰ yᴰ}{gᴰ : CatIsoᴰ g xᴰ yᴰ}
    (fᴰfunᴰ≡gᴰfunᴰ : Path Cᴰ.Hom[ _ , _ ]
        (_ , fᴰ .CatIsoᴰ.funᴰ)
        (_ , gᴰ .CatIsoᴰ.funᴰ))
    where
    private
      ∫fᴰ≡∫gᴰ : Path Cᴰ.ISOC.Hom[ (x , xᴰ) , (y , yᴰ) ] (∫CatIso fᴰ) (∫CatIso gᴰ)
      ∫fᴰ≡∫gᴰ = Cᴰ.ISOC≡ fᴰfunᴰ≡gᴰfunᴰ
    opaque
      CatIsoᴰ≡ :
        Path (Σ[ f ∈ C.ISOC.Hom[ x , y ] ] CatIsoᴰ f xᴰ yᴰ)
            (_ , fᴰ)
            (_ , gᴰ)
      CatIsoᴰ≡ = ΣPathP (f≡g , fᴰ≡gᴰ) where
        f≡g : f ≡ g
        f≡g i .CatIso.fun = ∫fᴰ≡∫gᴰ i .CatIso.fun .fst
        f≡g i .CatIso.inv = ∫fᴰ≡∫gᴰ i .CatIso.inv .fst
        f≡g i .CatIso.sec = isSet→Square C.isSetHom
          C.⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.inv .fst) ⟩⋆⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.fun .fst) ⟩
          (refl {x = C.id {y}})
          (f .CatIso.sec)
          ((g .CatIso.sec))
          i
        f≡g i .CatIso.ret = isSet→Square C.isSetHom
          C.⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.fun .fst) ⟩⋆⟨ (λ i → ∫fᴰ≡∫gᴰ i .CatIso.inv .fst) ⟩
          (refl {x = C.id {x}})
          (f .CatIso.ret)
          (g .CatIso.ret)
          i
        fᴰ≡gᴰ : PathP (λ i → CatIsoᴰ (f≡g i) xᴰ yᴰ) fᴰ gᴰ
        fᴰ≡gᴰ i .CatIsoᴰ.funᴰ = ∫fᴰ≡∫gᴰ i .CatIso.fun .snd
        fᴰ≡gᴰ i .CatIsoᴰ.invᴰ = ∫fᴰ≡∫gᴰ i .CatIso.inv .snd
        fᴰ≡gᴰ i .CatIsoᴰ.secᴰ = ∫fᴰ≡∫gᴰ i .CatIso.sec
        fᴰ≡gᴰ i .CatIsoᴰ.retᴰ = ∫fᴰ≡∫gᴰ i .CatIso.ret

      CatIsoᴰPathP : ∀ {f≡g : f ≡ g}
        → PathP (λ i → CatIsoᴰ (f≡g i) xᴰ yᴰ) fᴰ gᴰ
      CatIsoᴰPathP {f≡g} =
        TypeRectify (λ j i → CatIsoᴰ (lem j i) xᴰ yᴰ)
          (PathPΣ CatIsoᴰ≡ .snd)
        where
          lem : (PathPΣ CatIsoᴰ≡ .fst) ≡ f≡g
          lem = C.ISOC.isSetHom _ _ _ _

  idCatIsoᴰ : ∀ {x}{xᴰ : Cobᴰ x} → CatIsoᴰ C.ISOC.id xᴰ xᴰ
  idCatIsoᴰ .CatIsoᴰ.funᴰ = Cᴰ.idᴰ
  idCatIsoᴰ .CatIsoᴰ.invᴰ = Cᴰ.idᴰ
  idCatIsoᴰ .CatIsoᴰ.secᴰ = Cᴰ.⋆IdL _
  idCatIsoᴰ .CatIsoᴰ.retᴰ = Cᴰ.⋆IdL _

  ⋆CatIsoᴰ : ∀ {x y z xᴰ yᴰ zᴰ}
    {f : CatIso C x y}
    {g : CatIso C y z}
    (fᴰ : CatIsoᴰ f xᴰ yᴰ)
    (gᴰ : CatIsoᴰ g yᴰ zᴰ)
    → CatIsoᴰ (f C.ISOC.⋆ g) xᴰ zᴰ
  ⋆CatIsoᴰ fᴰ gᴰ = isoᴰ
    (∫fᴰ⋆∫gᴰ .CatIso.fun .snd)
    (∫fᴰ⋆∫gᴰ .CatIso.inv .snd)
    (∫fᴰ⋆∫gᴰ .CatIso.sec)
    (∫fᴰ⋆∫gᴰ .CatIso.ret)
    where
    ∫fᴰ⋆∫gᴰ = ∫CatIso fᴰ Cᴰ.ISOC.⋆ ∫CatIso gᴰ

  ISOᴰ : Categoryᴰ C.ISOC Cobᴰ _
  ISOᴰ .Hom[_][_,_] = CatIsoᴰ
  ISOᴰ .idᴰ = idCatIsoᴰ
  ISOᴰ ._⋆ᴰ_ = ⋆CatIsoᴰ
  ISOᴰ .⋆IdLᴰ fᴰ = CatIsoᴰ≡ (Cᴰ.⋆IdLᴰ (fᴰ .CatIsoᴰ.funᴰ))
  ISOᴰ .⋆IdRᴰ fᴰ = CatIsoᴰ≡ (Cᴰ.⋆IdRᴰ (fᴰ .CatIsoᴰ.funᴰ))
  ISOᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ = CatIsoᴰ≡ $ Cᴰ.⋆Assocᴰ _ _ _
  ISOᴰ .isSetHomᴰ = isSetIso CatIsoᴰIsoΣ (isSetΣ Cᴰ.isSetHomᴰ (λ _ → isSetΣ Cᴰ.isSetHomᴰ
    λ _ → isProp→isSet (isProp× (Cᴰ.isSetHom _ _) (Cᴰ.isSetHom _ _))))

  CatIsoⱽ : {x : Cob}(xᴰ yᴰ : Cobᴰ x) → Type _
  CatIsoⱽ = CatIsoᴰ (idCatIso C)

  CatIsoⱽ→CatIsoFiber : ∀ {x}{xᴰ yᴰ : Cobᴰ x}
    (fⱽ : CatIsoⱽ xᴰ yᴰ)
    → CatIso Cᴰ.v[ x ] xᴰ yᴰ
  CatIsoⱽ→CatIsoFiber fⱽ .CatIso.fun = fⱽ .CatIsoᴰ.funᴰ
  CatIsoⱽ→CatIsoFiber fⱽ .CatIso.inv = fⱽ .CatIsoᴰ.invᴰ
  CatIsoⱽ→CatIsoFiber fⱽ .CatIso.sec = Cᴰ.rectify $ Cᴰ.≡out $
    sym (Cᴰ.reind-filler _ _) ∙ fⱽ .CatIsoᴰ.secᴰ
  CatIsoⱽ→CatIsoFiber fⱽ .CatIso.ret = Cᴰ.rectify $ Cᴰ.≡out $
    sym (Cᴰ.reind-filler _ _) ∙ fⱽ .CatIsoᴰ.retᴰ

  module CategoryᴰNotation where
    open Categoryᴰ Cᴰ public
    ISOCᴰ = ISOᴰ
    module ISOCᴰ = Categoryᴰ ISOᴰ
    ISOCᴰ≡ :
      ∀ {x y : Cob}{f g : C.ISOC.Hom[ x , y ]}
      {xᴰ yᴰ}{fᴰ : ISOCᴰ.Hom[ f ][ xᴰ , yᴰ ]}{gᴰ : ISOCᴰ.Hom[ g ][ xᴰ , yᴰ ]}
      → fᴰ .CatIsoᴰ.funᴰ Cᴰ.∫≡ gᴰ .CatIsoᴰ.funᴰ
      → fᴰ ISOCᴰ.∫≡ gᴰ
    ISOCᴰ≡ = CatIsoᴰ≡

    invCatIsoᴰ : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
      → (fᴰ : CatIsoᴰ f xᴰ yᴰ)
      → CatIsoᴰ (C.invCatIso f) yᴰ xᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.funᴰ = fᴰ .CatIsoᴰ.invᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.invᴰ = fᴰ .CatIsoᴰ.funᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.secᴰ = fᴰ .CatIsoᴰ.retᴰ
    invCatIsoᴰ fᴰ .CatIsoᴰ.retᴰ = fᴰ .CatIsoᴰ.secᴰ

    -- Can probably get this from ∫ somehow
    CatIsoᴰ⋆ᴰ-Iso-over : ∀ {x y xᴰ yᴰ}{f : C.ISOC.Hom[ x , y ]}
      → CatIsoᴰ f xᴰ yᴰ
      → ∀ {z}{zᴰ : Cobᴰ z}
      → IsoOver (C.CatIso⋆-Iso f) Cᴰ.Hom[_][ yᴰ , zᴰ ] Cᴰ.Hom[_][ xᴰ , zᴰ ]
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.fun g gᴰ = fᴰ .CatIsoᴰ.funᴰ Cᴰ.⋆ᴰ gᴰ
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.inv g gᴰ = fᴰ .CatIsoᴰ.invᴰ Cᴰ.⋆ᴰ gᴰ
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.rightInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.retᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _
    CatIsoᴰ⋆ᴰ-Iso-over fᴰ .IsoOver.leftInv g gᴰ = Cᴰ.rectify $ Cᴰ.≡out $
      sym (Cᴰ.⋆Assoc _ _ _) ∙ Cᴰ.⟨ fᴰ .CatIsoᴰ.secᴰ ⟩⋆⟨⟩ ∙ Cᴰ.⋆IdL _

module _ {C : Category Cob CHom-ℓ}{Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ} where
  private
    module Cᴰ = CategoryᴰNotation Cᴰ
  module CategoryᴰOver∫Notation
    (Dᴰ : Categoryᴰ (∫C Cᴰ) Dobᴰ DHom-ℓᴰ)
    where
    private
      module Dᴰ = Categoryᴰ Dᴰ
    open CategoryᴰNotation Dᴰ public

    vᴰ[_] : (c : Cob) → Categoryᴰ Cᴰ.v[ c ] (λ cᴰ → Dobᴰ (c , cᴰ)) _
    vᴰ[ c ] .Hom[_][_,_] fᴰ xᴰ yᴰ = Dᴰ.Hom[ (id C , fᴰ) ][ xᴰ , yᴰ ]
    vᴰ[ c ] .idᴰ = Dᴰ.idᴰ
    vᴰ[ c ] ._⋆ᴰ_ fᴰ gᴰ = Dᴰ.reind (Cᴰ.reind-filler _ _) $ (fᴰ Dᴰ.⋆ᴰ gᴰ)
    vᴰ[ c ] .⋆IdLᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdLᴰ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⋆IdLᴰ _))
    vᴰ[ c ] .⋆IdRᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdRᴰ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⋆IdRᴰ _))
    vᴰ[ c ] .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Cᴰ.⋆Assocᴰ _ _ _
          ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
          ),
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆Assocᴰ _ _ _
          ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.reind-filler _ _
          ))
    vᴰ[ c ] .isSetHomᴰ = Dᴰ.isSetHomᴰ

  module CategoryᴰOver∫SFNotation
    {Dob-ℓᴰ}{Dobᴰ}{DHom-ℓᴰ}
    (Dᴰ : SmallFibersCategoryᴰ (∫C Cᴰ) Dob-ℓᴰ Dobᴰ DHom-ℓᴰ)
    where
    private
      module Dᴰ = Categoryᴰ Dᴰ
    open CategoryᴰNotation Dᴰ public

    vᴰ[_]SF : (c : Cob) →
      SmallFibersCategoryᴰ Cᴰ.v[ c ] _
        (λ cᴰ → Dobᴰ (c , cᴰ))
        _
    vᴰ[ c ]SF .Hom[_][_,_] fᴰ xᴰ yᴰ = Dᴰ.Hom[ (id C , fᴰ) ][ xᴰ , yᴰ ]
    vᴰ[ c ]SF .idᴰ = Dᴰ.idᴰ
    vᴰ[ c ]SF ._⋆ᴰ_ fᴰ gᴰ = Dᴰ.reind (Cᴰ.reind-filler _ _) $ (fᴰ Dᴰ.⋆ᴰ gᴰ)
    vᴰ[ c ]SF .⋆IdLᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdLᴰ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⋆IdLᴰ _))
    vᴰ[ c ]SF .⋆IdRᴰ fᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⋆IdRᴰ _) ,
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⋆IdRᴰ _))
    vᴰ[ c ]SF .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (Cᴰ.rectify $ Cᴰ.≡out $
          (sym $ Cᴰ.reind-filler _ _)
          ∙ Cᴰ.⟨ sym $ Cᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Cᴰ.⋆Assocᴰ _ _ _
          ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler _ _ ⟩
          ∙ Cᴰ.reind-filler _ _
          ),
        (Dᴰ.rectify $ Dᴰ.≡out $
          (sym $ Dᴰ.reind-filler _ _)
          ∙ Dᴰ.⟨ sym $ Dᴰ.reind-filler _ _ ⟩⋆⟨⟩
          ∙ Dᴰ.⋆Assocᴰ _ _ _
          ∙ Dᴰ.⟨⟩⋆⟨ Dᴰ.reind-filler _ _ ⟩
          ∙ Dᴰ.reind-filler _ _
          ))
    vᴰ[ c ]SF .isSetHomᴰ = Dᴰ.isSetHomᴰ

module _
  {C : Category Cob CHom-ℓ}
  (Cᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ) where
  private
    module C = CategoryNotation C
    module Cᴰ = Categoryᴰ Cᴰ

  module _
    (idᴰ' : ∀ {x : Cob} {xᴰ : Cobᴰ x} →
       Σ[ fᴰ ∈ Cᴰ.Hom[ C.id ][ xᴰ , xᴰ ] ] Cᴰ.idᴰ ≡ fᴰ)
    (⋆ᴰ' : ∀ {x y z : Cob}
       {f : C.Hom[ x , y ]} {g : C.Hom[ y , z ]}
       {xᴰ : Cobᴰ x} {yᴰ : Cobᴰ y} {zᴰ : Cobᴰ z} →
       (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ]) →
       (gᴰ : Cᴰ.Hom[ g ][ yᴰ , zᴰ ]) →
       Σ[ hᴰ ∈ Cᴰ.Hom[ f C.⋆ g ][ xᴰ , zᴰ ] ] (fᴰ Cᴰ.⋆ᴰ gᴰ) ≡ hᴰ)
    where

    redefine-idᴰ-⋆ᴰ : Categoryᴰ C Cobᴰ CHom-ℓᴰ
    redefine-idᴰ-⋆ᴰ .Hom[_][_,_] = Cᴰ.Hom[_][_,_]
    redefine-idᴰ-⋆ᴰ .idᴰ = idᴰ' .fst
    redefine-idᴰ-⋆ᴰ ._⋆ᴰ_ fᴰ gᴰ = ⋆ᴰ' fᴰ gᴰ .fst
    redefine-idᴰ-⋆ᴰ .⋆IdLᴰ fᴰ =
      ΣPathP (
        (C.⋆IdL _) ,
        subst (λ gᴰ → gᴰ Cᴰ.≡[ C.⋆IdL _ ] fᴰ)
          (⋆ᴰ' Cᴰ.idᴰ fᴰ .snd
          ∙ cong₂ (λ u v → ⋆ᴰ' u v .fst) (idᴰ' .snd) refl)
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdLᴰ _))
    redefine-idᴰ-⋆ᴰ .⋆IdRᴰ fᴰ =
      ΣPathP (
        (C.⋆IdR _) ,
        subst (λ gᴰ → gᴰ Cᴰ.≡[ C.⋆IdR _ ] fᴰ)
          (⋆ᴰ' fᴰ Cᴰ.idᴰ .snd
          ∙ cong₂ (λ u v → ⋆ᴰ' u v .fst) refl (idᴰ' .snd))
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆IdRᴰ _))
    redefine-idᴰ-⋆ᴰ .⋆Assocᴰ fᴰ gᴰ hᴰ =
      ΣPathP (
        (C.⋆Assoc _ _ _) ,
        subst2
          (λ u v → u Cᴰ.≡[ C.⋆Assoc _ _ _ ] v)
          (⋆ᴰ' (fᴰ Cᴰ.⋆ᴰ gᴰ) hᴰ .snd
          ∙ cong (λ z → ⋆ᴰ' z hᴰ .fst) (⋆ᴰ' fᴰ gᴰ .snd))
          (⋆ᴰ' fᴰ (gᴰ Cᴰ.⋆ᴰ hᴰ) .snd
          ∙ cong (λ z → ⋆ᴰ' fᴰ z .fst) (⋆ᴰ' gᴰ hᴰ .snd))
          (Cᴰ.rectify $ Cᴰ.≡out $ Cᴰ.⋆Assocᴰ _ _ _)
        )
    redefine-idᴰ-⋆ᴰ .isSetHomᴰ = Cᴰ.isSetHomᴰ

-- Variants of smallness for displayed categories.
-- SmallObjectsCategoryᴰ
--   : ∀ (C : Category Cob C-ℓ)
--   → {ℓC}(ob : Type ℓC)(C-ℓ : ob → ob → Level)
--   → Typeω
-- SmallObjectsCategoryᴰ ob C-ℓ = Category (Liftω ob) λ (liftω x) (liftω y) → C-ℓ x y

-- -- A (LS) Category such that all hom sets are at the *same* universe level
-- GloballySmallCategory : (Cob : Typeω)(ℓC' : Level) → Typeω
-- GloballySmallCategory Cob ℓC' = Category Cob λ _ _ → ℓC'

-- -- A category is small if it both has small objects and is globally
-- -- small.
-- -- This is the only variant that is itself a small type: the
-- -- definition of Category in Cubical.Categories.Category
-- SmallCategory : ∀ ℓC (ℓC' : Level) → Typeω
-- SmallCategory ℓC ℓC' = Σω[ (liftω ob) ∈ Liftω (Type ℓC) ] GloballySmallCategory (Liftω ob) ℓC'



-- -- LEVEL-iso : ∀ {ℓ} {ℓ'} → SmallCategory.CatIso LEVEL ℓ ℓ'
-- -- LEVEL-iso .fst = tt
-- -- LEVEL-iso .snd .SmallCategory.isIso.inv = tt
-- -- LEVEL-iso .snd .SmallCategory.isIso.sec = refl
-- -- LEVEL-iso .snd .SmallCategory.isIso.ret = refl

-- -- LEVELω-iso : ∀ {ℓ} {ℓ'} → CatIso LEVELω ℓ ℓ'
-- -- LEVELω-iso .CatIso.fun = tt
-- -- LEVELω-iso .CatIso.inv = tt
-- -- LEVELω-iso .CatIso.sec = refl
-- -- LEVELω-iso .CatIso.ret = refl


-- -- -- module SET = LocallySmallCategoryᴰNotation SET
-- -- -- -- The total category LocallySmallCategoryᴰ.∫C SET is the "large category of all small sets"
-- -- -- -- Then
-- -- -- SETᴰ : LocallySmallCategoryᴰ
-- -- --          (LEVEL ⊘ LocallySmallCategoryᴰ.∫C SET)
-- -- --          (λ (ℓᴰ , (_ , liftω X)) → Liftω (⟨ X ⟩ → hSet ℓᴰ))
-- -- -- SETᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
-- -- -- SETᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] (_ , _ , f) (liftω Xᴰ) (liftω Yᴰ) =
-- -- --   ∀ x → ⟨ Xᴰ x ⟩ → ⟨ Yᴰ (f x ) ⟩
-- -- -- SETᴰ .LocallySmallCategoryᴰ.idᴰ = λ x xᴰ → xᴰ
-- -- -- SETᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ {f = (_ , _ , f)} fᴰ gᴰ x xᴰ =
-- -- --   gᴰ (f x) (fᴰ x xᴰ)
-- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ = λ _ → refl
-- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ = λ _ → refl
-- -- -- SETᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ = λ _ _ _ → refl
-- -- -- SETᴰ .LocallySmallCategoryᴰ.isSetHomᴰ {yᴰ = liftω Yᴰ} =
-- -- --   isSetΠ λ _ → isSet→ (Yᴰ _ .snd)

-- -- -- module SETᴰ = LocallySmallCategoryᴰNotation SETᴰ

-- -- -- module _ (C : LocallySmallCategory Cob) (D : LocallySmallCategory Dob) where
-- -- --   private
-- -- --     module D = LocallySmallCategory D
-- -- --   weaken : LocallySmallCategoryᴰ C λ _ → Dob
-- -- --   weaken .LocallySmallCategoryᴰ.Hom-ℓᴰ _ x _ y = D.Hom-ℓ x y
-- -- --   weaken .LocallySmallCategoryᴰ.Hom[_][_,_] _ = D.Hom[_,_]
-- -- --   weaken .LocallySmallCategoryᴰ.idᴰ = D.id
-- -- --   weaken .LocallySmallCategoryᴰ._⋆ᴰ_ = D._⋆_
-- -- --   weaken .LocallySmallCategoryᴰ.⋆IdLᴰ = D.⋆IdL
-- -- --   weaken .LocallySmallCategoryᴰ.⋆IdRᴰ = D.⋆IdR
-- -- --   weaken .LocallySmallCategoryᴰ.⋆Assocᴰ = D.⋆Assoc
-- -- --   weaken .LocallySmallCategoryᴰ.isSetHomᴰ = D.isSetHom
