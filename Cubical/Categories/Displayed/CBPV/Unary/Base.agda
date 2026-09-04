-- A (Unary) CBPVCat is a category displayed over KIND, i.e., the free category 𝓥 → 𝓒
-- U and F types are defined as (op)cartesian lifts of the morphism 𝓥 → 𝓒.
-- A CBPVCat with U/F types is a MultCBPVCat i.e. "multiplicative"

-- A CBPVCatᴰ over C is a cat displayed over ∫ C.

-- A MultCBPVCatⱽ over a CBPVCat C has all (op)cartesian lifts of morphisms over 𝓥 → 𝓒

-- A MultCBPVCatᴰ over a MultCBPVCat has displayed U/F as defined below
{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function

open import Cubical.Prop

import Cubical.Data.Equality as Eq
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration.Displayed
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓᴰᴰ ℓᴰᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

CBPVCat : ∀ ℓ ℓ' → Type _
CBPVCat = Categoryᴰ KIND

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  ValueOb : Type ℓ
  ValueOb = C.ob[ 𝓥 ]

  ComputationOb : Type ℓ
  ComputationOb = C.ob[ 𝓒 ]

KINDAssoc : EqPsh.ReprEqAssoc KIND
KINDAssoc _ _ _ _ _ _ = Eq.refl

KIND^opAssoc : EqPsh.ReprEqAssoc (KIND ^op)
KIND^opAssoc _ _ _ _ _ _ = Eq.refl

module _ (C : CBPVCat ℓ ℓ') where
  private
    module C = Categoryᴰ C

  U-Spec : (B : C.ob[ 𝓒 ]) → Presheafⱽ 𝓥 C ℓ'
  U-Spec B = reindPshᴰNatTrans (yoRec (KIND [-, 𝓒 ]) _) (C [-][-, B ])

  -- N.b.: this implies that C is a fibration because the only other
  -- morphisms in the base are identities
  hasU : Type _
  hasU = Quadrable C {x = 𝓥}{y = 𝓒} _

  -- This is better because KIND is strict category
  hasUEq : Type _
  hasUEq = ∀ (B : C.ob[ 𝓒 ]) → EqPsh.CartesianLift C KINDAssoc
    {x = 𝓥}{y = 𝓒}
    _
    B

  -- this similarly implies that C is an opfibration
  hasF : Type _
  hasF = Quadrable (C ^opᴰ) {x = 𝓒}{y = 𝓥} _

  hasFEq : Type _
  hasFEq = ∀ (A : C.ob[ 𝓥 ]) → EqPsh.CartesianLift (C ^opᴰ) KIND^opAssoc
    {x = 𝓒}{y = 𝓥}
    _
    A

  CBPVCatᴰ : ∀ ℓᴰ ℓᴰ' → Type _
  CBPVCatᴰ = Categoryᴰ (∫C C)

MultCBPVCat : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MultCBPVCat ℓ ℓ' =
  Σ[ C ∈ CBPVCat ℓ ℓ' ] hasU C × hasF C

MultCBPVCatEq : ∀ ℓ ℓ' → Type (ℓ-suc (ℓ-max ℓ ℓ'))
MultCBPVCatEq ℓ ℓ' =
  Σ[ C ∈ CBPVCat ℓ ℓ' ] hasUEq C × hasFEq C

forgetEq : MultCBPVCatEq ℓ ℓ' → MultCBPVCat ℓ ℓ'
forgetEq C .fst = C .fst
forgetEq C .snd .fst B =
  EqCartesianLift→CartesianLift
    KINDAssoc
    (C .fst)
    B
    𝓥
    _
    (C .snd .fst B)
forgetEq C .snd .snd A =
  EqCartesianLift→CartesianLift
    KIND^opAssoc
    (C .fst ^opᴰ)
    A
    𝓒
    _
    (C .snd .snd A)

module _ {C : CBPVCat ℓ ℓ'}(Cᴰ : CBPVCatᴰ C ℓᴰ ℓᴰ') where
  private
    module C = Categoryᴰ C
    module Cᴰ = Fibers Cᴰ

  hasUⱽ : Type _
  hasUⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable Cᴰ (_ , f)

  hasFⱽ : Type _
  hasFⱽ = ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}(f : C [ _ ][ A , B ]) → Quadrable (Cᴰ ^opᴰᴰ) (_ , f)

  hasUᴰ : hasU C → Type _
  hasUᴰ = Liftsᴰ⁺ⱽ.Quadrableᴰ _ _ Cᴰ {k1 = 𝓥}{k2 = 𝓒} _

  hasFᴰ : hasF C → Type _
  hasFᴰ = Liftsᴰ⁺ⱽ.Quadrableᴰ _ _ (Cᴰ ^opᴰᴰ) {k1 = 𝓒}{k2 = 𝓥} _

  -- Notation for the displayed U/F types. The displayed β/η laws are
  -- instances of the generic cartesian-lift laws in
  -- Liftsᴰ⁺ⱽ.CartesianLiftᴰNotation, rectified along caller-supplied
  -- paths for the base force/ret and β/η. These give a clean interface
  -- to the eliminators for free CBPV models.
  module _ (hasUC : hasU C) (hasUᴰC : hasUᴰ hasUC) where
    private
      module ∫Ccat = Category (∫C C)
      module Uᴰ {B} {Bᴰ : Cᴰ.ob[ 𝓒 , B ]} =
        Liftsᴰ⁺ⱽ.QuadrableᴰNotation KIND C Cᴰ _ hasUC hasUᴰC {Bᴰ = Bᴰ}

      U-ob : C.ob[ 𝓒 ] → C.ob[ 𝓥 ]
      U-ob B = hasUC B .fst

      U-force : ∀ {B} → C [ ı tt ][ U-ob B , B ]
      U-force = QuadrableNotation.πⱽ C hasUC

      U-thunk : ∀ {A B} → C [ ı tt ][ A , B ]
        → C [ Category.id KIND ][ A , U-ob B ]
      U-thunk = QuadrableNotation.introᴰ C hasUC

    forceᴰ : ∀ {B : C.ob[ 𝓒 ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      → Cᴰ.Hom[ _ , QuadrableNotation.πⱽ C hasUC ][ hasUᴰC Bᴰ .fst , Bᴰ ]
    forceᴰ = Uᴰ.πⱽ

    thunkᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      (M : C [ ı tt ][ A , B ])
      → Cᴰ.Hom[ ı tt , M ][ Aᴰ , Bᴰ ]
      → Cᴰ.Hom[ ı tt , QuadrableNotation.introᴰ C hasUC M ][ Aᴰ , hasUᴰC Bᴰ .fst ]
    thunkᴰ M Mᴰ = Uᴰ.introᴰ Mᴰ

    Uβᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      {force : C [ ı tt ][ hasUC B .fst , B ]}
      (U-force≡force : Path ∫Ccat.Hom[ _ , _ ] (_ , U-force) (_ , force))
      (M : C [ ı tt ][ A , B ])
      (Uβ : Path ∫Ccat.Hom[ _ , _ ]
        (ı tt , U-thunk M C.⋆ᴰ force) (ı tt , M))
      (Mᴰ : Cᴰ.Hom[ ı tt , M ][ Aᴰ , Bᴰ ])
      → PathP (λ i → (Cᴰ .Categoryᴰ.Hom[_][_,_]) (Uβ i) Aᴰ Bᴰ)
          (thunkᴰ M Mᴰ Cᴰ.⋆ᴰ Cᴰ.reind U-force≡force forceᴰ)
          Mᴰ
    Uβᴰ U-force≡force M Uβ Mᴰ = Cᴰ.rectify {e' = Uβ} $ Cᴰ.≡out $
      Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler⁻ U-force≡force ⟩ ∙ Uᴰ.βᴰ' Mᴰ

    Uηᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      {force : C [ ı tt ][ hasUC B .fst , B ]}
      (U-force≡force : Path ∫Ccat.Hom[ _ , _ ] (_ , U-force) (_ , force))
      (V : C [ Category.id KIND ][ A , hasUC B .fst ])
      (Uη : Path ∫Ccat.Hom[ _ , _ ]
        (Category.id KIND , V)
        (Category.id KIND , U-thunk (V C.⋆ᴰ force)))
      (Vᴰ : Cᴰ.Hom[ Category.id KIND , V ][ Aᴰ , hasUᴰC Bᴰ .fst ])
      → PathP (λ i → (Cᴰ .Categoryᴰ.Hom[_][_,_]) (Uη i)
          Aᴰ (hasUᴰC Bᴰ .fst))
          Vᴰ
          (thunkᴰ (V C.⋆ᴰ force)
            (Vᴰ Cᴰ.⋆ᴰ Cᴰ.reind U-force≡force forceᴰ))
    Uηᴰ U-force≡force V Uη Vᴰ = Cᴰ.rectify {e' = Uη} $ Cᴰ.≡out $
      Uᴰ.ηᴰ Vᴰ
      ∙ Uᴰ.cong-introᴰ
          (Uᴰ.⋆πⱽ≡⋆ᴰπⱽ Vᴰ ∙ Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler U-force≡force ⟩)

  module _ (hasFC : hasF C) (hasFᴰC : hasFᴰ hasFC) where
    private
      module ∫Ccat = Category (∫C C)
      module Fᴰ {A} {Aᴰ : Cᴰ.ob[ 𝓥 , A ]} =
        Liftsᴰ⁺ⱽ.QuadrableᴰNotation (KIND ^op) (C ^opᴰ) (Cᴰ ^opᴰᴰ) _
          hasFC hasFᴰC {Bᴰ = Aᴰ}

      F-ob : C.ob[ 𝓥 ] → C.ob[ 𝓒 ]
      F-ob A = hasFC A .fst

      F-ret : ∀ {A} → C [ ı tt ][ A , F-ob A ]
      F-ret = QuadrableNotation.πⱽ (C ^opᴰ) hasFC

      F-bind : ∀ {A B} → C [ ı tt ][ A , B ]
        → C [ Category.id KIND ][ F-ob A , B ]
      F-bind = QuadrableNotation.introᴰ (C ^opᴰ) hasFC

    F-retᴰ : ∀ {A : C.ob[ 𝓥 ]}{Aᴰ : Cᴰ.ob[ 𝓥 , A ]}
      → Cᴰ.Hom[ ı tt , F-ret ][ Aᴰ , hasFᴰC Aᴰ .fst ]
    F-retᴰ = Fᴰ.πⱽ

    F-bindᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      (M : C [ ı tt ][ A , B ])
      → Cᴰ.Hom[ ı tt , M ][ Aᴰ , Bᴰ ]
      → (Cᴰ .Categoryᴰ.Hom[_][_,_])
          (Category.id KIND , F-bind M)
          (hasFᴰC Aᴰ .fst) Bᴰ
    F-bindᴰ M Mᴰ = Fᴰ.introᴰ Mᴰ

    Fβᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      {ret : C [ ı tt ][ A , hasFC A .fst ]}
      (F-ret≡ret : Path ∫Ccat.Hom[ _ , _ ] (_ , F-ret) (_ , ret))
      (M : C [ ı tt ][ A , B ])
      (Fβ : Path ∫Ccat.Hom[ _ , _ ]
        (ı tt , ret C.⋆ᴰ F-bind M) (ı tt , M))
      (Mᴰ : Cᴰ.Hom[ ı tt , M ][ Aᴰ , Bᴰ ])
      → PathP (λ i → (Cᴰ .Categoryᴰ.Hom[_][_,_]) (Fβ i) Aᴰ Bᴰ)
          (Cᴰ.reind F-ret≡ret F-retᴰ Cᴰ.⋆ᴰ F-bindᴰ M Mᴰ)
          Mᴰ
    Fβᴰ F-ret≡ret M Fβ Mᴰ = Cᴰ.rectify {e' = Fβ} $ Cᴰ.≡out $
      Cᴰ.⟨ Cᴰ.reind-filler⁻ F-ret≡ret ⟩⋆⟨⟩ ∙ Fᴰ.βᴰ' Mᴰ

    Fηᴰ : ∀ {A : C.ob[ 𝓥 ]}{B : C.ob[ 𝓒 ]}
      {Aᴰ : Cᴰ.ob[ 𝓥 , A ]}{Bᴰ : Cᴰ.ob[ 𝓒 , B ]}
      {ret : C [ ı tt ][ A , hasFC A .fst ]}
      (F-ret≡ret : Path ∫Ccat.Hom[ _ , _ ] (_ , F-ret) (_ , ret))
      (K : C [ Category.id KIND ][ hasFC A .fst , B ])
      (Fη : Path ∫Ccat.Hom[ _ , _ ]
        (Category.id KIND , K)
        (Category.id KIND , F-bind (ret C.⋆ᴰ K)))
      (Kᴰ : Cᴰ.Hom[ Category.id KIND , K ][ hasFᴰC Aᴰ .fst , Bᴰ ])
      → PathP (λ i → (Cᴰ .Categoryᴰ.Hom[_][_,_]) (Fη i)
          (hasFᴰC Aᴰ .fst) Bᴰ)
          Kᴰ
          (F-bindᴰ (ret C.⋆ᴰ K)
            (Cᴰ.reind F-ret≡ret F-retᴰ Cᴰ.⋆ᴰ Kᴰ))
    Fηᴰ F-ret≡ret K Fη Kᴰ = Cᴰ.rectify {e' = Fη} $ Cᴰ.≡out $
      Fᴰ.ηᴰ Kᴰ
      ∙ Fᴰ.cong-introᴰ
          (Fᴰ.⋆πⱽ≡⋆ᴰπⱽ Kᴰ ∙ Cᴰ.⟨ Cᴰ.reind-filler F-ret≡ret ⟩⋆⟨⟩)

  module _ (hasUC : hasU C) where
    hasUⱽ→ᴰ : hasUⱽ → hasUᴰ hasUC
    hasUⱽ→ᴰ Uⱽ =
      Liftsᴰ⁺ⱽ.Quadrableⱽ→ᴰ KIND C Cᴰ _ hasUC (Uⱽ _)

  module _ (hasFC : hasF C) where
    hasFⱽ→ᴰ : hasFⱽ → hasFᴰ hasFC
    hasFⱽ→ᴰ Fⱽ =
      Liftsᴰ⁺ⱽ.Quadrableⱽ→ᴰ (KIND ^op) (C ^opᴰ) (Cᴰ ^opᴰᴰ) _ hasFC (Fⱽ _)

MultCBPVCatⱽ : ∀ (C : CBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type (ℓ-suc ((ℓ ⊔ℓ ℓ') ⊔ℓ (ℓᴰ ⊔ℓ ℓᴰ')))
MultCBPVCatⱽ C ℓᴰ ℓᴰ' =
  Σ[ Cᴰ ∈ CBPVCatᴰ C ℓᴰ ℓᴰ' ] hasUⱽ Cᴰ × hasFⱽ Cᴰ

MultCBPVCatᴰ : ∀ (C : MultCBPVCat ℓ ℓ') ℓᴰ ℓᴰ' → Type (ℓ-suc ((ℓ ⊔ℓ ℓ') ⊔ℓ (ℓᴰ ⊔ℓ ℓᴰ')))
MultCBPVCatᴰ C ℓᴰ ℓᴰ' =
  Σ[ Cᴰ ∈ CBPVCatᴰ (C .fst) ℓᴰ ℓᴰ' ]
  hasUᴰ Cᴰ (C .snd .fst)
  × hasFᴰ Cᴰ (C .snd .snd)

MultCBPVCatⱽ→ᴰ : {C : MultCBPVCat ℓ ℓ'}
  → MultCBPVCatⱽ (C .fst) ℓᴰ ℓᴰ'
  → MultCBPVCatᴰ C ℓᴰ ℓᴰ'
MultCBPVCatⱽ→ᴰ Cⱽ .fst = Cⱽ .fst
MultCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .fst =
  hasUⱽ→ᴰ (Cⱽ .fst) (C .snd .fst) (Cⱽ .snd .fst)
MultCBPVCatⱽ→ᴰ {C = C} Cⱽ .snd .snd =
  hasFⱽ→ᴰ (Cⱽ .fst) (C .snd .snd) (Cⱽ .snd .snd)

module _
  {C : CBPVCat ℓ ℓ'} {D : CBPVCat ℓ'' ℓᴰ}
  (Dⱽ : MultCBPVCatⱽ D ℓᴰᴰ ℓᴰᴰ')
  (F : Functorⱽ C D)
  where

  hasUⱽReindex : hasUⱽ (reindex (Dⱽ .fst) (∫F F))
  hasUⱽReindex f yᴰ =
    reindexCartesianLift (Dⱽ .fst) (∫F F) (_ , f) yᴰ
      (Dⱽ .snd .fst (F .Functorᴰ.F-homᴰ f) yᴰ)

  hasFⱽReindex : hasFⱽ (reindex (Dⱽ .fst) (∫F F))
  hasFⱽReindex f yᴰ =
    f*yᴰ .fst ,
    pshiso
      (pshhom
        (λ x → f*yᴰ .snd .PshIso.trans .PshHom.N-ob x)
        (λ c c' g p →
          f*yᴰ .snd .PshIso.trans .PshHom.N-hom c c' g p))
      (f*yᴰ .snd .PshIso.nIso)
    where
    f*yᴰ =
      reindexCartesianLift
        (Dⱽ .fst ^opᴰᴰ)
        (∫F (F ^opFⱽ))
        (_ , f)
        yᴰ
        (Dⱽ .snd .snd (F .Functorᴰ.F-homᴰ f) yᴰ)

  MultCBPVCatⱽReindex : MultCBPVCatⱽ C ℓᴰᴰ ℓᴰᴰ'
  MultCBPVCatⱽReindex .fst =
    reindex (Dⱽ .fst) (∫F F)
  MultCBPVCatⱽReindex .snd .fst =
    hasUⱽReindex
  MultCBPVCatⱽReindex .snd .snd =
    hasFⱽReindex
