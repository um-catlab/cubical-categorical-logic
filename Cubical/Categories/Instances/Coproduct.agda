-- The coproduct of two categories, with its universal property
module Cubical.Categories.Instances.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sum as Sum hiding (rec; elim; _⊎_)
open import Cubical.Data.Empty as Empty hiding (rec; elim)

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Functor.Base

open import Cubical.Categories.Displayed.Section.Base
open import Cubical.Categories.Displayed.Instances.Weaken as Weaken
open import Cubical.Categories.Displayed.Instances.Reindex.Base as Reindex
open import Cubical.Categories.Displayed.Instances.Path as PathC

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Functorᴰ
open Section

module _ (C : Category ℓC ℓC')(D : Category ℓD ℓD') where
  private
    ⊎Ob = C .ob Sum.⊎ D .ob

    Hom⊎ : ⊎Ob → ⊎Ob → Type (ℓ-max ℓC' ℓD')
    Hom⊎ (inl c) (inl c') = Lift ℓD' $ C [ c , c' ]
    Hom⊎ (inr d) (inr d') = Lift ℓC' $ D [ d , d' ]
    Hom⊎ (inl c) (inr d') = ⊥*
    Hom⊎ (inr d) (inl c') = ⊥*

    -- the following inductive definition is isomorphic and very
    -- slightly more ergonomic, but lives at a higher universe level
    data Hom⊎' : ⊎Ob → ⊎Ob → Type (ℓ-max (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')) where
      inl : ∀ {c c'} → C [ c , c' ] → Hom⊎' (inl c) (inl c')
      inr : ∀ {d d'} → D [ d , d' ] → Hom⊎' (inr d) (inr d')

  _⊎_ : Category (ℓ-max ℓC ℓD) (ℓ-max ℓC' ℓD')
  _⊎_ .ob = ⊎Ob
  _⊎_ .Hom[_,_] = Hom⊎
  _⊎_ .id {inl c} = lift $ C .id
  _⊎_ .id {inr d} = lift $ D .id
  _⊎_ ._⋆_ {inl c} {inl c'} {inl c''} f g = lift (f .lower ⋆⟨ C ⟩ g .lower )
  _⊎_ ._⋆_ {inr d} {inr d'} {inr d''} f g = lift (f .lower ⋆⟨ D ⟩ g .lower)
  _⊎_ .⋆IdL {inl _} {inl _} f = cong lift (C .⋆IdL (f .lower))
  _⊎_ .⋆IdL {inr _} {inr _} f = cong lift (D .⋆IdL (f .lower))
  _⊎_ .⋆IdR {inl _} {inl _} f = cong lift (C .⋆IdR (f .lower))
  _⊎_ .⋆IdR {inr _} {inr _} f = cong lift (D .⋆IdR (f .lower))
  _⊎_ .⋆Assoc {inl _} {inl _} {inl _} {inl _} f g h =
    cong lift (C .⋆Assoc (f .lower) (g .lower) (h .lower))
  _⊎_ .⋆Assoc {inr _} {inr _} {inr _} {inr _} f g h =
    cong lift (D .⋆Assoc (f .lower) (g .lower) (h .lower))
  _⊎_ .isSetHom {inl _} {inl _} = isOfHLevelLift 2 (C .isSetHom)
  _⊎_ .isSetHom {inr _} {inr _} = isOfHLevelLift 2 (D .isSetHom)
  _⊎_ .isSetHom {inl _} {inr _} = isProp→isSet isProp⊥*
  _⊎_ .isSetHom {inr _} {inl _} = isProp→isSet isProp⊥*

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'} where
  -- TODO: should these be inl and inr?
  Inl : Functor C (C ⊎ D)
  Inl .F-ob = inl
  Inl .F-hom = lift
  Inl .F-id = refl
  Inl .F-seq _ _ = refl

  Inr : Functor D (C ⊎ D)
  Inr .F-ob = inr
  Inr .F-hom = lift
  Inr .F-id = refl
  Inr .F-seq _ _ = refl

  module _ {Cᴰ : Categoryᴰ (C ⊎ D) ℓCᴰ ℓDᴰ}
           (inl-case : Section Inl Cᴰ)
           (inr-case : Section Inr Cᴰ)
         where
    elim : GlobalSection Cᴰ
    elim .F-obᴰ (inl c) = inl-case .F-obᴰ c
    elim .F-obᴰ (inr d) = inr-case .F-obᴰ d
    elim .F-homᴰ {inl _} {inl _} f = inl-case .F-homᴰ (f .lower)
    elim .F-homᴰ {inr _} {inr _} f = inr-case .F-homᴰ (f .lower)
    elim .F-idᴰ {inl _} = inl-case .F-idᴰ
    elim .F-idᴰ {inr _} = inr-case .F-idᴰ
    elim .F-seqᴰ {inl _} {inl _} {inl _} f g =
      inl-case .F-seqᴰ (f .lower) (g .lower)
    elim .F-seqᴰ {inr _} {inr _} {inr _} f g =
      inr-case .F-seqᴰ (f .lower) (g .lower)

  module _ {E : Category ℓE ℓE'}
           {F : Functor (C ⊎ D) E}
           {Cᴰ : Categoryᴰ E ℓCᴰ ℓCᴰ'}
           (inl-case : Section (F ∘F Inl) Cᴰ)
           (inr-case : Section (F ∘F Inr) Cᴰ)
         where
    elimLocal : Section F Cᴰ
    elimLocal = GlobalSectionReindex→Section _ _
      (elim (Reindex.introS _ inl-case) (Reindex.introS _ inr-case))

  module _ {E : Category ℓE ℓE'}
           (inl-case : Functor C E)
           (inr-case : Functor D E)
         where
    rec : Functor (C ⊎ D) E
    rec = Weaken.introS⁻ {F = _}
      (elim (Weaken.introS _ inl-case)
            (Weaken.introS _ inr-case))
  module _ {E : Category ℓE ℓE'}
           {F G : Functor (C ⊎ D) E}
           (inl-case : F ∘F Inl ≡ G ∘F Inl)
           (inr-case : F ∘F Inr ≡ G ∘F Inr)
         where
    extensionality : F ≡ G
    extensionality = PathReflection (elimLocal
      (reindS (Functor≡ (λ _ → refl) (λ _ → refl)) (PathReflection⁻ inl-case))
      (reindS (Functor≡ (λ _ → refl) (λ _ → refl)) (PathReflection⁻ inr-case)))

  -- TODO: a version of extensionality for sections
  -- TODO: a version of extensionality that produces a NatIso instead of a path
