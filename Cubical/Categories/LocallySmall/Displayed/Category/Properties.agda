module Cubical.Categories.LocallySmall.Displayed.Category.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Foundations.More
  using (isSet→Square)
  renaming (rectify to TypeRectify)

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.More

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Categories.LocallySmall.Category.Base

open import Cubical.Categories.LocallySmall.Displayed.Category.Base
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
