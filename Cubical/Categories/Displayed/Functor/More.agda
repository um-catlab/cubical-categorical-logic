{-# OPTIONS --safe #-}
--
module Cubical.Categories.Displayed.Functor.More where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Functor
import      Cubical.Data.Equality as Eq

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Constructions.Weaken.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

private
  variable
    ℓ ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  where
  open Functor
  open Functorᴰ
  -- Only use this if H is not refl on ob/hom, otherwise use reindF' below
  reindF : ∀ {G}(H : F ≡ G) → Functorᴰ F Cᴰ Dᴰ → Functorᴰ G Cᴰ Dᴰ
  reindF H = subst (λ F → Functorᴰ F Cᴰ Dᴰ) H

  private
    module C = Category C
    module D = Category D
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module R = HomᴰReasoning Dᴰ

    GF-ob-ty = Eq.singl (F .F-ob)
    GF-hom-ty : GF-ob-ty → Type _
    GF-hom-ty GF-ob = Eq.singlP
      (Eq.ap (λ G-ob → ∀ {x}{y} → C [ x , y ] → D [ G-ob x , G-ob y ])
             (GF-ob .snd))
      (F .F-hom)
  module _ (Fᴰ : Functorᴰ F Cᴰ Dᴰ) where
    open Functor
    reindF'-ob : (GF-ob : GF-ob-ty) → ∀ {x} → Cᴰ.ob[ x ] → Dᴰ.ob[ GF-ob .fst x ]
    reindF'-ob (_ , Eq.refl) = Fᴰ .F-obᴰ

    reindF'-hom : (GF-ob : GF-ob-ty) (GF-hom : GF-hom-ty GF-ob)
                → ∀ {x y}{f : C [ x , y ]}{xᴰ}{yᴰ}
                → Cᴰ [ f ][ xᴰ , yᴰ ]
                → Dᴰ [ GF-hom .fst f
                    ][ reindF'-ob GF-ob xᴰ
                     , reindF'-ob GF-ob yᴰ ]
    reindF'-hom (_ , Eq.refl) (_ , Eq.refl) = Fᴰ .F-homᴰ

    reindF'-id : (GF-ob : GF-ob-ty) (GF-hom : GF-hom-ty GF-ob)
      (GF-id : ∀ {x} → GF-hom .fst (C.id {x}) ≡ D.id)
      → ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
      → reindF'-hom GF-ob GF-hom (Cᴰ.idᴰ {x}{xᴰ}) Dᴰ.≡[ GF-id ] Dᴰ.idᴰ
    reindF'-id (_ , Eq.refl) (_ , Eq.refl) GF-id = R.rectify (Fᴰ .F-idᴰ)

    reindF'-seq : (GF-ob : GF-ob-ty) (GF-hom : GF-hom-ty GF-ob)
      (GF-seq : ∀ {x}{y}{z}(f : C [ x , y ])(g : C [ y , z ])
        → GF-hom .fst (f C.⋆ g) ≡ (GF-hom .fst f) D.⋆ GF-hom .fst g)
      → ∀ {x}{y}{z}{f : C [ x , y ]}{g : C [ y , z ]}{xᴰ}{yᴰ}{zᴰ}
      → (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ]) →
      reindF'-hom GF-ob GF-hom
      (fᴰ Cᴰ.⋆ᴰ gᴰ) Dᴰ.≡[ GF-seq f g ]
      reindF'-hom GF-ob GF-hom fᴰ Dᴰ.⋆ᴰ reindF'-hom GF-ob GF-hom gᴰ
    reindF'-seq (_ , Eq.refl) (_ , Eq.refl) GF-seq fᴰ gᴰ =
      R.rectify (Fᴰ .F-seqᴰ fᴰ gᴰ)

  open Functor
  -- This is preferable to reindF if the equalities are Refl.
  reindF' : (G : Functor C D)
            (GF-ob≡FF-ob : F .F-ob Eq.≡ G .F-ob)
            (GF-hom≡FF-hom :
              Eq.HEq (Eq.ap (λ F-ob₁ → ∀ {x} {y}
                         → C [ x , y ] → D [ F-ob₁ x , F-ob₁ y ])
                         GF-ob≡FF-ob)
                (F .F-hom)
                (G .F-hom))
          → Functorᴰ F Cᴰ Dᴰ
          → Functorᴰ G Cᴰ Dᴰ
  reindF' G GF-ob≡FF-ob GF-hom≡FF-hom Fᴰ = record
    { F-obᴰ  = reindF'-ob Fᴰ GF-ob
    ; F-homᴰ = reindF'-hom Fᴰ GF-ob GF-hom
    ; F-idᴰ  = reindF'-id Fᴰ GF-ob GF-hom (G .F-id)
    ; F-seqᴰ = reindF'-seq Fᴰ GF-ob GF-hom (G .F-seq)
    } where
      GF-ob : GF-ob-ty
      GF-ob = _ , GF-ob≡FF-ob

      GF-hom : GF-hom-ty GF-ob
      GF-hom = _ , GF-hom≡FF-hom

Functorᵛ : {C : Category ℓC ℓC'}
  → Categoryᴰ C ℓCᴰ ℓCᴰ' → Categoryᴰ C ℓDᴰ ℓDᴰ'
  → Type _
Functorᵛ = Functorᴰ Id

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ C ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᵛ Dᴰ Eᴰ) (Fᴰ : Functorᵛ Cᴰ Dᴰ)
  where

  funcCompᵛ : Functorᵛ Cᴰ Eᴰ
  funcCompᵛ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)

  _∘Fᵛ_ = funcCompᵛ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ D ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᵛ Dᴰ Eᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  funcCompᵛᴰ : Functorᴰ F Cᴰ Eᴰ
  funcCompᵛᴰ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)

  _∘Fᵛᴰ_ = funcCompᵛᴰ

module _ {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  {G : Functor D E}
  {Cᴰ : Categoryᴰ D ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Fᴰ : Functorᵛ Cᴰ Dᴰ)
  where

  funcCompᴰᵛ : Functorᴰ G Cᴰ Eᴰ
  funcCompᴰᵛ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)
  _∘Fᴰᵛ_ = funcCompᴰᵛ

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  (Fᵛ : Functorᵛ Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFᵛ : Functorᵛ (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFᵛ = reindF' _ Eq.refl Eq.refl (Fᵛ ^opFᴰ)
