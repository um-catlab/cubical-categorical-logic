--
module Cubical.Categories.Displayed.Functor.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category.Base hiding (isIso)
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Functor
import      Cubical.Data.Equality as Eq
import      Cubical.Data.Equality.More as Eq

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Instances.Weaken.Base
import      Cubical.Categories.Displayed.Reasoning as HomᴰReasoning

open import Cubical.Reflection.RecordEquiv.More

private
  variable
    ℓ ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓE ℓE' ℓEᴰ ℓEᴰ' : Level

Idᴰ : {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} → Functorᴰ Id Cᴰ Cᴰ
Idᴰ = 𝟙ᴰ⟨ _ ⟩

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

  module _
    (G : Functor C D)
    (GF-ob≡FF-ob : F .F-ob Eq.≡ G .F-ob)
    (GF-hom≡FF-hom :
      Eq.HEq (Eq.ap (λ F-ob₁ → ∀ {x} {y}
                  → C [ x , y ] → D [ F-ob₁ x , F-ob₁ y ])
                  GF-ob≡FF-ob)
        (F .F-hom)
        (G .F-hom))
    (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    where

    private
      GF-ob : GF-ob-ty
      GF-ob = _ , GF-ob≡FF-ob

      GF-hom : GF-hom-ty GF-ob
      GF-hom = _ , GF-hom≡FF-hom

    -- This is preferable to reindF if the equalities are Refl.
    reindF' : Functorᴰ G Cᴰ Dᴰ
    reindF' .F-obᴰ  = reindF'-ob Fᴰ GF-ob
    reindF' .F-homᴰ = reindF'-hom Fᴰ GF-ob GF-hom
    reindF' .F-idᴰ  = reindF'-id Fᴰ GF-ob GF-hom (G .F-id)
    reindF' .F-seqᴰ = reindF'-seq Fᴰ GF-ob GF-hom (G .F-seq)

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

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
  where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ
    module Fᴰ = Functorᴰ Fᴰ
  FullyFaithfulᴰ : Type _
  FullyFaithfulᴰ = ∀ {x y}(f : C [ x , y ])(xᴰ : Cᴰ.ob[ x ])(yᴰ : Cᴰ.ob[ y ])
    → isIso {A = Cᴰ.Hom[ f ][ xᴰ , yᴰ ]}{B = Dᴰ.Hom[ F ⟪ f ⟫ ][ Fᴰ.F-obᴰ xᴰ , Fᴰ.F-obᴰ yᴰ ]} Fᴰ.F-homᴰ

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {F : Functor C D}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  where
  open Category
  open Functor
  open Functorᴰ
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Dᴰ = Categoryᴰ Dᴰ

  FunctorᴰΣ : Type _
  FunctorᴰΣ =
    Σ[ F-obᴰ ∈ ({x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ]) ]
    Σ[ F-homᴰ ∈ ({x y : C .ob} {f : C [ x , y ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
      → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ]) ]
    Σ[ F-idᴰ ∈ ({x : C .ob} {xᴰ : Cᴰ.ob[ x ]}
      → PathP (λ i → Dᴰ.Hom[ F .F-id i ][ F-obᴰ xᴰ , F-obᴰ xᴰ ])
          (F-homᴰ (Cᴰ.idᴰ {p = xᴰ})) (Dᴰ.idᴰ {p = F-obᴰ xᴰ})) ]
    ({x y z : C .ob} {f : C [ x , y ]} {g : C [ y , z ]}
      {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]} {zᴰ : Cᴰ.ob[ z ]}
      (fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]) (gᴰ : Cᴰ [ g ][ yᴰ , zᴰ ])
      → PathP (λ i → Dᴰ.Hom[ F .F-seq f g i ][ F-obᴰ xᴰ , F-obᴰ zᴰ ])
          (F-homᴰ (fᴰ Cᴰ.⋆ᴰ gᴰ)) (F-homᴰ fᴰ Dᴰ.⋆ᴰ F-homᴰ gᴰ))

  FunctorᴰΣIso : Iso (Functorᴰ F Cᴰ Dᴰ) FunctorᴰΣ
  unquoteDef FunctorᴰΣIso = defineRecordIsoΣ FunctorᴰΣIso (quote Functorᴰ)

  isSetFunctorᴰ : isSet FunctorᴰΣ → isSet (Functorᴰ F Cᴰ Dᴰ)
  isSetFunctorᴰ = isOfHLevelRetractFromIso 2 FunctorᴰΣIso

  module _ (propHoms : hasPropHoms Dᴰ) where
    isPropF-homᴰΣ :
      (F-obᴰ : {x : C.ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → isProp
      ({x y : C .ob} {f : C [ x , y ]}
        {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
        → Cᴰ [ f ][ xᴰ , yᴰ ] → Dᴰ [ F .F-hom f ][ F-obᴰ xᴰ , F-obᴰ yᴰ ])
    isPropF-homᴰΣ F-obᴰ = isPropImplicitΠ λ x → isPropImplicitΠ λ y →
      isPropImplicitΠ λ f → isPropImplicitΠ λ xᴰ → isPropImplicitΠ λ yᴰ →
      isPropΠ λ _ → propHoms (F .F-hom f) (F-obᴰ xᴰ) (F-obᴰ yᴰ)

    isSetFunctorᴰΣPropHoms :
      isSet ({x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → isSet FunctorᴰΣ
    isSetFunctorᴰΣPropHoms isSetOb = isSetΣSndProp isSetOb λ F-obᴰ →
      isPropΣ (isPropF-homᴰΣ F-obᴰ) λ F-homᴰ →
      isPropΣ
        (isPropImplicitΠ λ x → isPropImplicitΠ λ xᴰ →
          isOfHLevelPathP' 1 Dᴰ.isSetHomᴰ _ _)
        (λ _ → isPropImplicitΠ λ x → isPropImplicitΠ λ y → isPropImplicitΠ λ z →
          isPropImplicitΠ λ f → isPropImplicitΠ λ g →
          isPropImplicitΠ λ xᴰ → isPropImplicitΠ λ yᴰ → isPropImplicitΠ λ zᴰ →
          isPropΠ2 λ fᴰ gᴰ → isOfHLevelPathP' 1 Dᴰ.isSetHomᴰ _ _)

    isSetFunctorᴰPropHoms :
      isSet ({x : C .ob} → Cᴰ.ob[ x ] → Dᴰ.ob[ F .F-ob x ])
      → isSet (Functorᴰ F Cᴰ Dᴰ)
    isSetFunctorᴰPropHoms isSetOb =
      isSetFunctorᴰ (isSetFunctorᴰΣPropHoms isSetOb)
