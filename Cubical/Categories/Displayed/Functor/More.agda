--
module Cubical.Categories.Displayed.Functor.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Functor
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.NaturalTransformation.More
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.IsoFibration
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

  reindF'' : (G : Functor C D)
             (GF-ob≡FF-ob : F .F-ob Eq.≡ G .F-ob)
             (GF-hom≡FF-hom :
              Eq.mixedHEq (Eq.ap (λ F-ob₁ → ∀ {x} {y}
                         → C [ x , y ] → D [ F-ob₁ x , F-ob₁ y ])
                         GF-ob≡FF-ob)
                (F .F-hom)
                (G .F-hom)
                )
          → Functorᴰ F Cᴰ Dᴰ
          → Functorᴰ G Cᴰ Dᴰ
  reindF'' G ob≡ hom≡ = reindF' G ob≡ (Eq.pathToEq hom≡)

Functorⱽ : {C : Category ℓC ℓC'}
  → Categoryᴰ C ℓCᴰ ℓCᴰ' → Categoryᴰ C ℓDᴰ ℓDᴰ'
  → Type _
Functorⱽ = Functorᴰ Id

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'} {Eᴰ : Categoryᴰ C ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorⱽ Dᴰ Eᴰ) (Fᴰ : Functorⱽ Cᴰ Dᴰ)
  where

  funcCompⱽ : Functorⱽ Cᴰ Eᴰ
  funcCompⱽ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)

  _∘Fⱽ_ = funcCompⱽ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Eᴰ : Categoryᴰ D ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorⱽ Dᴰ Eᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where

  funcCompⱽᴰ : Functorᴰ F Cᴰ Eᴰ
  funcCompⱽᴰ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)

  _∘Fⱽᴰ_ = funcCompⱽᴰ

module _ {D : Category ℓD ℓD'} {E : Category ℓE ℓE'} {G : Functor D E}
  {Cᴰ : Categoryᴰ D ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {Eᴰ : Categoryᴰ E ℓEᴰ ℓEᴰ'}
  (Gᴰ : Functorᴰ G Dᴰ Eᴰ) (Fᴰ : Functorⱽ Cᴰ Dᴰ)
  where

  funcCompᴰⱽ : Functorᴰ G Cᴰ Eᴰ
  funcCompᴰⱽ = reindF' _ Eq.refl Eq.refl (Gᴰ ∘Fᴰ Fᴰ)
  _∘Fᴰⱽ_ = funcCompᴰⱽ

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  (Fⱽ : Functorⱽ Cᴰ Dᴰ)
  where
  open Functorᴰ
  _^opFⱽ : Functorⱽ (Cᴰ ^opᴰ) (Dᴰ ^opᴰ)
  _^opFⱽ = reindF' _ Eq.refl Eq.refl (Fⱽ ^opFᴰ)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ Gᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
  open Functorᴰ
  FunctorᴰEq : Type _
  FunctorᴰEq =
    Σ[ obᴰEq ∈ (Eq._≡_ {A = ∀ {x} → Cᴰ.ob[ x ] → Dᴰ.ob[ F ⟅ x ⟆ ]} (Fᴰ .F-obᴰ) (Gᴰ .F-obᴰ) ) ]
    Eq.HEq
      (Eq.ap (λ F-obᴰ → (∀ {x y} {f : C [ x , y ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ]
      → Dᴰ [ F ⟪ f ⟫ ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]))
        obᴰEq)
      (Fᴰ .F-homᴰ)
      (Gᴰ .F-homᴰ)


-- Reindexing a functor by a NatIso
module _
  {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {F : Functor C D}
  where
  open NatTrans
  open NatIso
  open Functor
  open Functorᴰ
  open isIso
  open isIsoᴰ
  private
    module D = Category D
    module Dᴰ = Fibers Dᴰ
  -- TODO: actually only need isoLifts for α
  reindFNIso : ∀ {G}(α : NatIso G F)
    → isIsoFibration Dᴰ
    → Functorᴰ F Cᴰ Dᴰ
    → Functorᴰ G Cᴰ Dᴰ
  reindFNIso α isoFib Fᴰ .F-obᴰ cᴰ = isoFib _ (NatIsoAt α _) .fst
  reindFNIso α isoFib Fᴰ .F-homᴰ fᴰ =
    Dᴰ.reind (D.⟨ refl ⟩⋆⟨ (symNatIso α) .trans .N-hom _ ⟩ ∙ (sym (D.⋆Assoc _ _ _) ∙ D.⟨ α .nIso _ .ret ⟩⋆⟨ refl ⟩) ∙ D.⋆IdL _) $
    isoFib _ (NatIsoAt α _) .snd .fst Dᴰ.⋆ᴰ Fᴰ .F-homᴰ fᴰ Dᴰ.⋆ᴰ isoFib _ (NatIsoAt α _) .snd .snd .invᴰ
  reindFNIso α isoFib Fᴰ .F-idᴰ = Dᴰ.rectify $ Dᴰ.≡out $
    sym (Dᴰ.reind-filler _ _)
    ∙ Dᴰ.⟨ refl ⟩⋆⟨ Dᴰ.⟨ ∫F Fᴰ .F-id  ⟩⋆⟨ refl ⟩ ∙ Dᴰ.⋆IdL _ ⟩
    ∙ (Dᴰ.≡in $ isoFib (F-obᴰ Fᴰ _) (NatIsoAt α _) .snd .snd .retᴰ)
  reindFNIso α isoFib Fᴰ .F-seqᴰ fᴰ gᴰ = Dᴰ.rectify $ Dᴰ.≡out $ sym $
    Dᴰ.⟨ (sym $ Dᴰ.reind-filler _ _) ∙ (sym $ Dᴰ.⋆Assoc _ _ _) ⟩⋆⟨ (sym $ Dᴰ.reind-filler _ _) ⟩
    ∙ Dᴰ.⋆Assoc _ _ _
    ∙ Dᴰ.⟨ refl ⟩⋆⟨ (sym $ Dᴰ.⋆Assoc _ _ _) ∙ Dᴰ.⟨ Dᴰ.≡in $ isoFib (F-obᴰ Fᴰ _) (NatIsoAt α _) .snd .snd .secᴰ ⟩⋆⟨ refl ⟩ ∙ Dᴰ.⋆IdL _ ⟩
    ∙ (Dᴰ.⋆Assoc _ _ _ ∙ Dᴰ.⟨ refl ⟩⋆⟨ sym (Dᴰ.⋆Assoc _ _ _) ∙ Dᴰ.⟨ sym $ ∫F Fᴰ .F-seq _ _ ⟩⋆⟨ refl ⟩ ⟩)
    ∙ Dᴰ.reind-filler _ _
    
