{-

The Full Image of a displayed functor.

Displayed analogue of Cubical.Categories.Instances.FullImage. Given
Fᴰ : Functorᴰ F Cᴰ Dᴰ, the displayed full image is the Categoryᴰ over
FullImage F whose displayed objects are those of Cᴰ and whose displayed
homs are reindexed displayed homs of Dᴰ along Fᴰ on objects.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.FullImage where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.FullImage
open import Cubical.Categories.Instances.Fiber

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
import      Cubical.Categories.Displayed.Reasoning as DispReasoning

private
  variable
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D)
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  FullImageᴰ : Categoryᴰ (FullImage F) ℓCᴰ ℓDᴰ'
  FullImageᴰ .ob[_] = Cᴰ .ob[_]
  FullImageᴰ .Hom[_][_,_] f xᴰ yᴰ =
    Dᴰ .Hom[_][_,_] f (Fᴰ .F-obᴰ xᴰ) (Fᴰ .F-obᴰ yᴰ)
  FullImageᴰ .idᴰ = Dᴰ .idᴰ
  FullImageᴰ ._⋆ᴰ_ = Dᴰ ._⋆ᴰ_
  FullImageᴰ .⋆IdLᴰ = Dᴰ .⋆IdLᴰ
  FullImageᴰ .⋆IdRᴰ = Dᴰ .⋆IdRᴰ
  FullImageᴰ .⋆Assocᴰ = Dᴰ .⋆Assocᴰ
  FullImageᴰ .isSetHomᴰ = Dᴰ .isSetHomᴰ

  ToFullImageᴰ : Functorᴰ (ToFullImage F) Cᴰ FullImageᴰ
  ToFullImageᴰ .F-obᴰ xᴰ = xᴰ
  ToFullImageᴰ .F-homᴰ = Fᴰ .F-homᴰ
  ToFullImageᴰ .F-idᴰ = Fᴰ .F-idᴰ
  ToFullImageᴰ .F-seqᴰ = Fᴰ .F-seqᴰ

  FromFullImageᴰ : Functorᴰ (FromFullImage F) FullImageᴰ Dᴰ
  FromFullImageᴰ .F-obᴰ = Fᴰ .F-obᴰ
  FromFullImageᴰ .F-homᴰ = λ z → z
  FromFullImageᴰ .F-idᴰ = refl
  FromFullImageᴰ .F-seqᴰ _ _ = refl

module _
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} (F : Functor C D)
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (isFullyFaithfulF : isFullyFaithful F)
  {Fᴰ : Functorᴰ F Cᴰ Dᴰ}
  (isFullyFaithfulFᴰ : FullyFaithfulᴰ Fᴰ)
  where

  private
    module C = Category C
    module D = Category D
    module Cᴰ = Fibers Cᴰ
    module Dᴰ = Fibers Dᴰ

    FC = FullImage F

    FF≃  : ∀ {x y} → C.Hom[ x , y ] ≃ D.Hom[ F .F-ob x , F .F-ob y ]
    FF≃ = _ , (isFullyFaithfulF _ _)

    HomᴰMap : ∀ {x y} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} →
      mapOver (FF≃ {x = x} {y = y} .fst)
        Cᴰ.Hom[_][ xᴰ , yᴰ ]
        Dᴰ.Hom[_][ Fᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ yᴰ ]
    HomᴰMap f fᴰ = Fᴰ .F-homᴰ fᴰ

    FF≃ᴰ-isEquiv : ∀ {x y} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → isEquivOver {P = Cᴰ.Hom[_][ xᴰ , yᴰ ]}
          {Q = Dᴰ.Hom[_][ Fᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ yᴰ ]}
          (HomᴰMap {x = x} {y = y} {xᴰ = xᴰ} {yᴰ = yᴰ})
    FF≃ᴰ-isEquiv {xᴰ = xᴰ} {yᴰ = yᴰ} f = isIsoToIsEquiv (isFullyFaithfulFᴰ f xᴰ yᴰ)

    FF≃ᴰ : ∀ {x y} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → IsoOver (equivToIso (FF≃ {x = x} {y = y}))
          (Cᴰ.Hom[_][ xᴰ , yᴰ ])
          (Dᴰ.Hom[_][ Fᴰ .F-obᴰ xᴰ , Fᴰ .F-obᴰ yᴰ ])
    FF≃ᴰ {xᴰ = xᴰ} {yᴰ = yᴰ} =
      equivOver→IsoOver FF≃ HomᴰMap (FF≃ᴰ-isEquiv {xᴰ = xᴰ} {yᴰ = yᴰ})

  invᴰ : Functorᴰ (inv isFullyFaithfulF) (FullImageᴰ F Fᴰ) Cᴰ
  invᴰ .F-obᴰ xᴰ = xᴰ
  invᴰ .F-homᴰ {f = g} = IsoOver.inv FF≃ᴰ g
  invᴰ .F-idᴰ {x = x} {xᴰ = xᴰ} =
    Cᴰ.rectifyOut $
      (sym $ Cᴰ.≡in $ λ i → IsoOver.inv FF≃ᴰ (F .F-id i) (Fᴰ .F-idᴰ i))
      ∙ Cᴰ.≡in (IsoOver.leftInv FF≃ᴰ C.id Cᴰ.idᴰ)
  invᴰ .F-seqᴰ {f = g} {g = h} {xᴰ = xᴰ} {yᴰ = yᴰ} {zᴰ = zᴰ} gᴰ hᴰ =
    -- This could be a lot cleaner
    Cᴰ.rectifyOut $
      (sym $ Cᴰ.≡in $ λ i → IsoOver.inv FF≃ᴰ
           ((isFullyFaithfulF _ _ .equiv-proof g .fst .snd i) D.⋆
             (isFullyFaithfulF _ _ .equiv-proof h .fst .snd i))
           (IsoOver.rightInv FF≃ᴰ g gᴰ i Dᴰ.⋆ᴰ IsoOver.rightInv FF≃ᴰ h hᴰ i))
      ∙ (sym $ Cᴰ.≡in $ λ i → IsoOver.inv FF≃ᴰ
        (F .F-seq (isFullyFaithfulF _ _ .equiv-proof g .fst .fst)
                  (isFullyFaithfulF _ _ .equiv-proof h .fst .fst) i)
        (Fᴰ .F-seqᴰ (IsoOver.inv FF≃ᴰ g gᴰ) (IsoOver.inv FF≃ᴰ h hᴰ) i))
      ∙ Cᴰ.≡in (IsoOver.leftInv FF≃ᴰ
                 (Iso.inv (equivToIso FF≃) g C.⋆ Iso.inv (equivToIso FF≃) h)
                 (IsoOver.inv FF≃ᴰ g gᴰ Cᴰ.⋆ᴰ IsoOver.inv FF≃ᴰ h hᴰ))

  invᴰ∘ToFullImageᴰ≡Idᴰ
    : PathP (λ i → Functorᴰ (inv∘ToFullImage≡Id isFullyFaithfulF i) Cᴰ Cᴰ)
        (invᴰ ∘Fᴰ ToFullImageᴰ F Fᴰ) 𝟙ᴰ⟨ Cᴰ ⟩
  invᴰ∘ToFullImageᴰ≡Idᴰ =
    Functorᴰ≡ {H = inv∘ToFullImage≡Id isFullyFaithfulF}
      (λ _ → refl)
      (λ {f = f} fᴰ → IsoOver.leftInv FF≃ᴰ f fᴰ)

  ToFullImageᴰ∘invᴰ≡Idᴰ
    : PathP (λ i → Functorᴰ (ToFullImage∘inv≡Id isFullyFaithfulF i)
              (FullImageᴰ F Fᴰ) (FullImageᴰ F Fᴰ))
        (ToFullImageᴰ F Fᴰ ∘Fᴰ invᴰ) 𝟙ᴰ⟨ FullImageᴰ F Fᴰ ⟩
  ToFullImageᴰ∘invᴰ≡Idᴰ =
    Functorᴰ≡ {H = ToFullImage∘inv≡Id isFullyFaithfulF}
      (λ _ → refl)
      (λ {f = f} fᴰ → IsoOver.rightInv FF≃ᴰ f fᴰ)
