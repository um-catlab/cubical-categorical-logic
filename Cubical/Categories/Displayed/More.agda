module Cubical.Categories.Displayed.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Data.Sigma
open import Cubical.Categories.Category.Base
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Functor
open import Cubical.Categories.Displayed.Base

private
  variable
    ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' : Level

module _ {C : Category ℓC ℓC'} (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ') where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  isSetDepHomᴰ : ∀ {x y}{xᴰ yᴰ} →
    isSetDep (λ (f : C [ x , y ]) → Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
  isSetDepHomᴰ = isSet→isSetDep (λ f → Cᴰ.isSetHomᴰ)

  isSetHomᴰ' : ∀ {x y}{xᴰ}{yᴰ}
    {f g : C [ x , y ]} {p q : f ≡ g}
    (fᴰ : Cᴰ.Hom[ f ][ xᴰ , yᴰ ])
    (gᴰ : Cᴰ.Hom[ g ][ xᴰ , yᴰ ])
    (pᴰ : fᴰ Cᴰ.≡[ p ] gᴰ )
    (qᴰ : fᴰ Cᴰ.≡[ q ] gᴰ )
    → ∀ i j → Cᴰ.Hom[  C.isSetHom f g p q i j ][ xᴰ , yᴰ ]
  isSetHomᴰ' fᴰ gᴰ pᴰ qᴰ i j = isSetDepHomᴰ fᴰ gᴰ pᴰ qᴰ (C.isSetHom _ _ _ _) i j

  CatIsoⱽ : ∀ {a} → Cᴰ.ob[ a ] → Cᴰ.ob[ a ] → Type _
  CatIsoⱽ = CatIsoᴰ Cᴰ idCatIso

  pathToCatIsoⱽ : ∀ {a}{aᴰ bᴰ : Cᴰ.ob[ a ]} → (aᴰ ≡ bᴰ) → CatIsoⱽ aᴰ bᴰ
  pathToCatIsoⱽ {aᴰ = aᴰ} = J (λ bᴰ _ → CatIsoⱽ aᴰ bᴰ) (idᴰCatIsoᴰ Cᴰ)

  CatIsoⱽ→CatIso : ∀ {a aᴰ aᴰ'}
    → CatIsoⱽ aᴰ aᴰ'
    → CatIso (Cᴰ.v[ a ]) aᴰ aᴰ'
  CatIsoⱽ→CatIso isoⱽ .fst = isoⱽ .fst
  CatIsoⱽ→CatIso isoⱽ .snd .isIso.inv = isoⱽ .snd .isIsoᴰ.invᴰ
  CatIsoⱽ→CatIso isoⱽ .snd .isIso.sec = Cᴰ.rectify $ Cᴰ.≡out $
    sym (Cᴰ.reind-filler _ _) ∙ (Cᴰ.≡in $ isoⱽ .snd .isIsoᴰ.secᴰ)
  CatIsoⱽ→CatIso isoⱽ .snd .isIso.ret = Cᴰ.rectify $ Cᴰ.≡out $
    sym (Cᴰ.reind-filler _ _) ∙ (Cᴰ.≡in $ isoⱽ .snd .isIsoᴰ.retᴰ)

  ∫CatIso : ∀ {a b aᴰ bᴰ}
    → (iso : CatIso C a b)
    → CatIsoᴰ Cᴰ iso aᴰ bᴰ
    → CatIso (∫C Cᴰ) (a , aᴰ) (b , bᴰ)
  ∫CatIso iso isoᴰ .fst = iso .fst , isoᴰ .fst
  ∫CatIso iso isoᴰ .snd .isIso.inv = iso .snd .isIso.inv , isoᴰ .snd .isIsoᴰ.invᴰ
  ∫CatIso iso isoᴰ .snd .isIso.sec = ΣPathP ((iso .snd .isIso.sec) , (isoᴰ .snd .isIsoᴰ.secᴰ))
  ∫CatIso iso isoᴰ .snd .isIso.ret = ΣPathP ((iso .snd .isIso.ret) , (isoᴰ .snd .isIsoᴰ.retᴰ))

  invIsoⱽ : ∀ {a} {aᴰ aᴰ' : Cᴰ.ob[ a ]}
    → CatIsoⱽ aᴰ aᴰ' → CatIsoⱽ aᴰ' aᴰ
  invIsoⱽ {a}{aᴰ}{aᴰ'} f = f .snd .isIsoᴰ.invᴰ , isisoᴰ (f .fst) (f .snd .isIsoᴰ.retᴰ) (f .snd .isIsoᴰ.secᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  where
  private
    module C = Category C
    module Cᴰ = Fibers Cᴰ
  module _ {c c'} {α : CatIso C c c'} {cᴰ : Cᴰ.ob[ c ]} {cᴰ' : Cᴰ.ob[ c' ]}
    (αᴰ : CatIsoᴰ Cᴰ α cᴰ cᴰ')
    where
    mkOpaquePathsCatIsoᴰ : CatIsoᴰ Cᴰ α cᴰ cᴰ'
    mkOpaquePathsCatIsoᴰ .fst = αᴰ .fst
    mkOpaquePathsCatIsoᴰ .snd .isIsoᴰ.invᴰ = αᴰ .snd .isIsoᴰ.invᴰ
    mkOpaquePathsCatIsoᴰ .snd .isIsoᴰ.secᴰ = the-secᴰ
      where
      opaque
        the-secᴰ : αᴰ .snd .isIsoᴰ.invᴰ Cᴰ.⋆ᴰ αᴰ .fst Cᴰ.≡[ α .snd .isIso.sec ] Cᴰ.idᴰ
        the-secᴰ = αᴰ .snd .isIsoᴰ.secᴰ
    mkOpaquePathsCatIsoᴰ .snd .isIsoᴰ.retᴰ = the-retᴰ
      where
      opaque
        the-retᴰ : αᴰ .fst Cᴰ.⋆ᴰ αᴰ .snd .isIsoᴰ.invᴰ Cᴰ.≡[ α .snd .isIso.ret ] Cᴰ.idᴰ
        the-retᴰ = αᴰ .snd .isIsoᴰ.retᴰ
