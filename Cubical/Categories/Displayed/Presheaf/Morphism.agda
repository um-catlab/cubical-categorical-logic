{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Prod.Base hiding (_×_)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
  using (NatTrans ; NatIso ; idTrans)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.LocallySmall
  using (LocallySmallCategory; LocallySmallCategoryᴰ; module LocallySmallCategoryᴰNotation;
        LEVEL; _⊘_; Liftω; Σω; _,_; liftω; mapω'; ⊘-iso; LEVEL-iso; LEVELω-iso)
import Cubical.Categories.LocallySmall as LocallySmall

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base hiding (PRESHEAFᴰ)

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓR ℓRᴰ ℓS ℓSᴰ : Level

open Functor
open Functorᴰ
open isIsoᴰ
open isIsoOver
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} where
  private
    module C = Category C
    PshC = PRESHEAF C
    module PshC = LocallySmallCategoryᴰNotation PshC
-- First, we do the bare minimum to define the displayed category of PshHoms
  module _ {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
    private
      module Cᴰ = Categoryᴰ Cᴰ
    module _ {P : Presheaf C ℓP}
      {Q : Presheaf C ℓQ}
      (α : PshHom P Q)
      (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
      (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      private
        module P = PresheafNotation P
        module Pᴰ = PresheafᴰNotation Pᴰ
        module Qᴰ = PresheafᴰNotation Qᴰ

      record PshHomᴰ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓC) where
        no-eta-equality
        constructor pshhomᴰ
        field
          N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]
          -- TODO: we should probably make this a Path in ∫Qᴰ
          N-homᴰ :
            ∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
            → {f : C [ x , y ]}{p : P.p[ y ]}
            → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
            → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
                Qᴰ.≡[ α .N-hom x y f p ]
              (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ)

        ∫PshHom : PshHom (∫P Pᴰ) (∫P Qᴰ)
        ∫PshHom .N-ob (x , xᴰ) (p , pᴰ) = (α .N-ob _ p) , (N-obᴰ pᴰ)
        ∫PshHom .N-hom _ _ (f , fᴰ) (p , pᴰ) = ΣPathP ((α .N-hom _ _ f p) , N-homᴰ)

        private
          module ∫Pᴰ = PresheafNotation (∫P Pᴰ)
          module ∫Qᴰ = PresheafNotation (∫P Qᴰ)

        opaque
          N-obᴰ⟨_⟩ :
            ∀ {xxᴰ}{ppᴰ ppᴰ'}
            → Path ∫Pᴰ.p[ xxᴰ ] ppᴰ ppᴰ'
            → Path ∫Qᴰ.p[ xxᴰ ] (_ , N-obᴰ (ppᴰ .snd)) (_ , N-obᴰ (ppᴰ' .snd))
          N-obᴰ⟨_⟩ = cong (∫PshHom .N-ob _)

      PshHomᴰΣ : Type _
      PshHomᴰΣ =
        Σ[ N-obᴰ ∈
             (∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]) ]
        (∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
            → {f : C [ x , y ]}{p : P.p[ y ]}
            → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
            → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
                Qᴰ.≡[ α .N-hom x y f p ]
              (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ))

      opaque
        isPropN-homᴰ :
          ∀ (N-obᴰ : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
               {p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]) →
          isProp (∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
              → {f : C [ x , y ]}{p : P.p[ y ]}
              → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
              → N-obᴰ (fᴰ Pᴰ.⋆ᴰ pᴰ)
                  Qᴰ.≡[ α .N-hom x y f p ]
                (fᴰ Qᴰ.⋆ᴰ N-obᴰ pᴰ))
        isPropN-homᴰ =
          λ _ → isPropImplicitΠ4 λ _ _ _ _ → isPropImplicitΠ4 λ _ _ _ _ →
            λ _ _ → isSet→SquareP (λ i j → F-obᴰ Qᴰ _ (α .N-hom _ _ _ _ j) .snd) _ _ _ _

        isSetPshHomᴰΣ : isSet PshHomᴰΣ
        isSetPshHomᴰΣ =
          isSetΣ
            (isSetImplicitΠ3 (λ c cᴰ p → isSetΠ (λ pᴰ → Qᴰ.isSetPshᴰ)))
            λ _ → isProp→isSet (isPropN-homᴰ _)

      PshHomᴰΣIso : Iso PshHomᴰ PshHomᴰΣ
      unquoteDef PshHomᴰΣIso = defineRecordIsoΣ PshHomᴰΣIso (quote (PshHomᴰ))

      opaque
        isSetPshHomᴰ : isSet PshHomᴰ
        isSetPshHomᴰ = isSetIso PshHomᴰΣIso isSetPshHomᴰΣ

    private
      variable
        P : Presheaf C ℓP
        Q : Presheaf C ℓQ
        R : Presheaf C ℓR
        Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ
        Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ
        Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ
        α : PshHom P Q
        β : PshHom Q R
        αᴰ : PshHomᴰ α Pᴰ Qᴰ
        βᴰ : PshHomᴰ β Qᴰ Rᴰ

    open PshHomᴰ
    idPshHomᴰ : PshHomᴰ idPshHom Pᴰ Pᴰ
    idPshHomᴰ .N-obᴰ = λ z → z
    idPshHomᴰ .N-homᴰ = refl

    _⋆PshHomᴰ_ :
      (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
      (βᴰ : PshHomᴰ β Qᴰ Rᴰ)
      → PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
    _⋆PshHomᴰ_ {Rᴰ = Rᴰ} αᴰ βᴰ = record
      { N-obᴰ = λ pᴰ → ∫⋆ .N-ob _ (_ , pᴰ) .snd
      ; N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .N-hom _ _ _ _
      } where
        module Rᴰ = PresheafᴰNotation Rᴰ
        ∫⋆ = ∫PshHom αᴰ ⋆PshHom ∫PshHom βᴰ
    infixr 9 _⋆PshHomᴰ_

    PshHomᴰPathP : ∀ {α β : PshHom P Q}
      → (α≡β : α ≡ β)
      → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
      → (βᴰ : PshHomᴰ β Pᴰ Qᴰ)
      → Type _
    PshHomᴰPathP {Pᴰ = Pᴰ}{Qᴰ = Qᴰ} α≡β αᴰ βᴰ = PathP (λ i → PshHomᴰ (α≡β i) Pᴰ Qᴰ) αᴰ βᴰ

    module _ {α β : PshHom P Q}{αᴰ : PshHomᴰ α Pᴰ Qᴰ}{βᴰ : PshHomᴰ β Pᴰ Qᴰ} where
      private
        module P = PresheafNotation P
        module Q = PresheafNotation Q
        module Pᴰ = PresheafᴰNotation Pᴰ
        module Qᴰ = PresheafᴰNotation Qᴰ
      makePshHomᴰPathP :
        ∀ (α≡β : α ≡ β)
        → (αᴰ≡βᴰ : ∀ {x}{xᴰ}{p : P.p[ x ]}
            → PathP (λ i → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α≡β i .N-ob x p ][ xᴰ ] )
                    (αᴰ .N-obᴰ)
                    (βᴰ .N-obᴰ))
        → PshHomᴰPathP α≡β αᴰ βᴰ
      makePshHomᴰPathP α≡β αᴰ≡βᴰ = fiberwiseIsoFunInjective (λ α → PshHomᴰΣIso α Pᴰ Qᴰ)
        (ΣPathPProp (λ αN-obᴰ → isPropImplicitΠ4 (λ _ _ _ _ → isPropImplicitΠ4 (λ _ _ _ _ →
          λ pf1 pf2 → isSet→SquareP (λ _ _ → Qᴰ.isSetPshᴰ) pf1 pf2 refl refl)))
          (implicitFunExt $ implicitFunExt $ implicitFunExt $ αᴰ≡βᴰ))
  open PshHomᴰ
  PRESHEAFᴰ : (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
    → LocallySmallCategoryᴰ
        (LEVEL ⊘ LocallySmallCategoryᴰ.∫C (PRESHEAF C))
        λ { (ℓPᴰ , (_ , liftω P)) → Liftω (Presheafᴰ P Cᴰ ℓPᴰ) }
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.Hom[_][_,_] (_ , _ , α) (liftω Pᴰ) (liftω Qᴰ) =
    PshHomᴰ α Pᴰ Qᴰ
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.idᴰ = idPshHomᴰ
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ._⋆ᴰ_ = _⋆PshHomᴰ_
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdLᴰ {yᴰ = liftω Qᴰ} αᴰ =
    makePshHomᴰPathP _
      (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
    where module Qᴰ = PresheafᴰNotation Qᴰ
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆IdRᴰ {yᴰ = liftω Qᴰ} αᴰ =
    makePshHomᴰPathP _
      (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
    where module Qᴰ = PresheafᴰNotation Qᴰ
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.⋆Assocᴰ {wᴰ = liftω Qᴰ} αᴰ βᴰ γᴰ =
    makePshHomᴰPathP _
      (funExt λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ refl)
    where module Qᴰ = PresheafᴰNotation Qᴰ
  PRESHEAFᴰ Cᴰ .LocallySmallCategoryᴰ.isSetHomᴰ = isSetPshHomᴰ _ _ _
  module _ {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'} where
    private
      module Cᴰ = Categoryᴰ Cᴰ
      PshCᴰ = PRESHEAFᴰ Cᴰ
      module PshCᴰ = LocallySmallCategoryᴰNotation PshCᴰ
      variable
        P : Presheaf C ℓP
        Q : Presheaf C ℓQ
        R : Presheaf C ℓR
        Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ
        Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ
        Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ
        α : PshHom P Q
        β : PshHom Q R
        αᴰ : PshHomᴰ α Pᴰ Qᴰ
        βᴰ : PshHomᴰ β Qᴰ Rᴰ
    -- Iso stuff
    module _ (αᴰ : PshHomᴰ α Pᴰ Qᴰ) where
      private
        module Pᴰ = PresheafᴰNotation Pᴰ
        module Qᴰ = PresheafᴰNotation Qᴰ
      isPshIsoᴰ : isPshIso α
        → Type _
      isPshIsoᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
        → Σ[ invᴰ ∈ (∀ {q} → Qᴰ.p[ q ][ xᴰ ] → Pᴰ.p[ αIsIso x .fst q ][ xᴰ ]) ]
          (∀ {q}(qᴰ : Qᴰ.p[ q ][ xᴰ ]) → Path Qᴰ.p[ _ ] (_ , αᴰ .N-obᴰ (invᴰ qᴰ)) (_ , qᴰ))
          × (∀ {p}(pᴰ : Pᴰ.p[ p ][ xᴰ ]) → Path Pᴰ.p[ _ ] (_ , invᴰ (αᴰ .N-obᴰ pᴰ)) (_ , pᴰ))
    module _ {P : Presheaf C ℓP}{Q : Presheaf C ℓQ} where
      -- Convenient abbreviation, but use PshCᴰ.⋆ⱽ etc for the operations
      PshHomⱽ : (α : PshHom P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) → Type _
      PshHomⱽ α Pᴰ Qᴰ = PshCᴰ.Hom[ _ , _ , α ][ liftω Pᴰ , liftω Qᴰ ]

      record PshIsoᴰ (α : PshIso P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
        : Type (ℓ-max ℓC $ ℓ-max ℓC' $ ℓ-max ℓCᴰ $ ℓ-max ℓCᴰ' $ ℓ-max ℓP $ ℓ-max ℓPᴰ $ ℓ-max ℓQ $ ℓQᴰ)
        where
        no-eta-equality
        constructor pshisoᴰ
        field
          transᴰ : PshHomᴰ (α .trans) Pᴰ Qᴰ
          nIsoᴰ  : isPshIsoᴰ transᴰ (α .nIso)

      PshCatIsoᴰ : (α : PshCatIso P Q) (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
        → Type _
      PshCatIsoᴰ α Pᴰ Qᴰ = PshCᴰ.ISOCᴰ.Hom[ ⊘-iso LEVEL _ LEVEL-iso (LocallySmall.∫CatIso _ α)
        ][ liftω Pᴰ , liftω Qᴰ ]

      ∫PshIso :  {α : PshIso P Q} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
        → (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) → PshIso (∫P Pᴰ) (∫P Qᴰ)
      ∫PshIso αᴰ .trans = ∫PshHom (αᴰ .PshIsoᴰ.transᴰ)
      ∫PshIso αᴰ .nIso xxᴰ .fst qqᴰ = _ , (αᴰ .PshIsoᴰ.nIsoᴰ .fst (qqᴰ .snd))
      ∫PshIso αᴰ .nIso xxᴰ .snd .fst = λ b → αᴰ .PshIsoᴰ.nIsoᴰ .snd .fst (b .snd)
      ∫PshIso αᴰ .nIso xxᴰ .snd .snd = λ a → αᴰ .PshIsoᴰ.nIsoᴰ .snd .snd (a .snd)

    invPshIsoᴰ : {α : PshIso P Q} {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
      → (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
      → PshIsoᴰ (invPshIso α) Qᴰ Pᴰ
    invPshIsoᴰ {Pᴰ = Pᴰ}{Qᴰ = Qᴰ} αᴰ = pshisoᴰ
      (pshhomᴰ (λ qᴰ → ∫αᴰ⁻ .trans .N-ob _ (_ , qᴰ) .snd)
               (Pᴰ.rectify $ Pᴰ.≡out $ ∫αᴰ⁻ .trans .N-hom _ _ _ _))
      ((αᴰ .PshIsoᴰ.transᴰ .N-obᴰ)
      , (αᴰ .PshIsoᴰ.nIsoᴰ .snd .snd)
      , (αᴰ .PshIsoᴰ.nIsoᴰ .snd .fst))
      where
      module Pᴰ = PresheafᴰNotation Pᴰ
      ∫αᴰ⁻ = invPshIso (∫PshIso αᴰ)

    module _ (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      private
        module P = PresheafNotation P
        module Q = PresheafNotation Q
        module Pᴰ = PresheafᴰNotation Pᴰ
        module Qᴰ = PresheafᴰNotation Qᴰ
      PshIsoᴰ→PshCatIsoᴰ : ∀ α (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) → PshCatIsoᴰ (PshIso→PshCatIso α) Pᴰ Qᴰ
      PshIsoᴰ→PshCatIsoᴰ α αᴰ .LocallySmall.CatIsoᴰ.funᴰ = αᴰ .PshIsoᴰ.transᴰ
      PshIsoᴰ→PshCatIsoᴰ α αᴰ .LocallySmall.CatIsoᴰ.invᴰ = invPshIsoᴰ αᴰ .PshIsoᴰ.transᴰ
      PshIsoᴰ→PshCatIsoᴰ α αᴰ .LocallySmall.CatIsoᴰ.secᴰ =
        ΣPathP (ΣPathP (refl , (PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.secᴰ))
          , makePshHomᴰPathP _ (funExt λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $ αᴰ .PshIsoᴰ.nIsoᴰ .snd .fst qᴰ))
      PshIsoᴰ→PshCatIsoᴰ α αᴰ .LocallySmall.CatIsoᴰ.retᴰ =
        ΣPathP (ΣPathP (refl , (PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.retᴰ))
          , makePshHomᴰPathP _ (funExt λ pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ αᴰ .PshIsoᴰ.nIsoᴰ .snd .snd pᴰ))

      PshCatIsoᴰ→PshIsoᴰ : ∀ α (αᴰ : PshCatIsoᴰ α Pᴰ Qᴰ) → PshIsoᴰ (PshCatIso→PshIso α) Pᴰ Qᴰ
      PshCatIsoᴰ→PshIsoᴰ α αᴰ .PshIsoᴰ.transᴰ = αᴰ .LocallySmall.CatIsoᴰ.funᴰ
      PshCatIsoᴰ→PshIsoᴰ α αᴰ .PshIsoᴰ.nIsoᴰ .fst = αᴰ .LocallySmall.CatIsoᴰ.invᴰ .N-obᴰ
      PshCatIsoᴰ→PshIsoᴰ α αᴰ .PshIsoᴰ.nIsoᴰ .snd .fst qᴰ = Qᴰ.≡in $
        λ i → αᴰ .LocallySmall.CatIsoᴰ.secᴰ i .snd .N-obᴰ qᴰ
      PshCatIsoᴰ→PshIsoᴰ α αᴰ .PshIsoᴰ.nIsoᴰ .snd .snd pᴰ = Pᴰ.≡in $
        λ i → αᴰ .LocallySmall.CatIsoᴰ.retᴰ i .snd .N-obᴰ pᴰ

      -- -- Do we actually need this? I don't really think so tbh
      -- PshIsoᴰ≅PshCatIsoᴰ : IsoOver (PshIso≅PshCatIso P Q)
      --   (λ α → PshIsoᴰ α Pᴰ Qᴰ)
      --   λ α → PshCatIsoᴰ α Pᴰ Qᴰ
      -- PshIsoᴰ≅PshCatIsoᴰ = isoover PshIsoᴰ→PshCatIsoᴰ PshCatIsoᴰ→PshIsoᴰ
      --   (λ α αᴰ → PshCᴰ.ISOCᴰ.rectify $ PshCᴰ.ISOCᴰ.≡out $ PshCᴰ.ISOCᴰ≡ refl)
      --   λ α αᴰ → {!makePshHomᴰPathP!}
      module _ {α β : PshHom P Q} where
        PshCᴰ-reind :
          (α≡β : α ≡ β)
          → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
          → PshHomᴰ β Pᴰ Qᴰ
        PshCᴰ-reind α≡β = PshCᴰ.reind (ΣPathP (refl , ΣPathP (refl , α≡β)))

        PshCᴰ-reind-N-ob :
          (α≡β : α .N-ob ≡ β .N-ob)
          → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
          → PshHomᴰ β Pᴰ Qᴰ
        PshCᴰ-reind-N-ob α≡β αᴰ .N-obᴰ p = Qᴰ.reind (funExt₂⁻ α≡β _ _) (αᴰ .N-obᴰ p)
        PshCᴰ-reind-N-ob α≡β αᴰ .N-homᴰ = Qᴰ.rectify $ Qᴰ.≡out $
          (sym $ Qᴰ.reind-filler _ _)
          ∙ ∫PshHom αᴰ .N-hom _ _ _ _
          ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩

        private
          module _ (αᴰ : PshHomᴰ α Pᴰ Qᴰ) where
            N-ob-Eq : ∀ (αsingl : Eq.singl (α .N-ob))
              → ∀ {x}{xᴰ}{p : P.p[ x ]}
                → (pᴰ : Pᴰ.p[ p ][ xᴰ ])
                → Qᴰ.p[ αsingl .fst x p ][ xᴰ ]
            N-ob-Eq (_ , Eq.refl) = αᴰ .N-obᴰ

            N-ob-Eq-filler : (αsingl : Eq.singl (α .N-ob))
              → ∀ {x}{xᴰ}{p : P.p[ x ]}
              → (pᴰ : Pᴰ.p[ p ][ xᴰ ])
              → N-ob-Eq αsingl pᴰ ≡ Qᴰ.reind (funExt₂⁻ (Eq.eqToPath (αsingl .snd)) x p) (αᴰ .N-obᴰ pᴰ)
            N-ob-Eq-filler (_ , Eq.refl) pᴰ = Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _
        PshCᴰ-reind-N-ob-Eq :
          (α≡β : α .N-ob Eq.≡ β .N-ob)
          → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
          → PshHomᴰ β Pᴰ Qᴰ
        PshCᴰ-reind-N-ob-Eq α≡β αᴰ = pshhomᴰ (N-ob-Eq αᴰ βsingl)
          (N-ob-Eq-filler αᴰ βsingl _
          ◁ (Qᴰ.rectify $ Qᴰ.≡out $
              (sym $ Qᴰ.reind-filler _ _)
              ∙ ∫PshHom αᴰ .N-hom _ _ _ _
              ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩)
          ▷ cong (_ Qᴰ.⋆ᴰ_) (sym $ N-ob-Eq-filler αᴰ βsingl _)) where
          βsingl : Eq.singl (α .N-ob)
          βsingl = (β .N-ob , α≡β)

        opaque
          PshCᴰ-reind-filler :
            (α≡β : α ≡ β)
            → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
            → Path PshCᴰ.Hom[ _ , _ ]
                (_ , αᴰ)
                (_ , PshCᴰ-reind α≡β αᴰ)
          PshCᴰ-reind-filler α≡β αᴰ =
            PshCᴰ.reind-filler (ΣPathP (refl , ΣPathP (refl , _))) αᴰ

          PshCᴰ-reind-N-ob-filler :
            (α≡β : α .N-ob ≡ β .N-ob)
            → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
            → Path PshCᴰ.Hom[ _ , _ ]
                (_ , αᴰ)
                (_ , PshCᴰ-reind-N-ob α≡β αᴰ)
          PshCᴰ-reind-N-ob-filler α≡β αᴰ =
            ΣPathP (ΣPathP (refl , ΣPathP (refl , _)) , (makePshHomᴰPathP (makePshHomPath α≡β)
              (funExt (λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _))))

          PshCᴰ-reind-N-ob-Eq-filler :
            (α≡β : α .N-ob Eq.≡ β .N-ob)
            → (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
            → Path PshCᴰ.Hom[ _ , _ ]
                (_ , αᴰ)
                (_ , PshCᴰ-reind-N-ob-Eq α≡β αᴰ)
          PshCᴰ-reind-N-ob-Eq-filler α≡β αᴰ = ΣPathP (ΣPathP (refl , ΣPathP (refl , _)) , (makePshHomᴰPathP (makePshHomPath (Eq.eqToPath α≡β))
              (funExt (λ pᴰ → Qᴰ.rectify $ Qᴰ.≡out $ Qᴰ.reind-filler _ _ ∙ Qᴰ.≡in (sym $ N-ob-Eq-filler αᴰ (β .N-ob , α≡β) pᴰ)))))

    module _ {α β : PshCatIso P Q} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)(Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
      PshCᴰ-reind-N-ob-Eq-PshIso :
        (α≡β : α .LocallySmall.CatIsoᴰ.funᴰ .N-ob Eq.≡ β .LocallySmall.CatIsoᴰ.funᴰ .N-ob)
        (α⁻≡β⁻ : α .LocallySmall.CatIsoᴰ.invᴰ .N-ob Eq.≡ β .LocallySmall.CatIsoᴰ.invᴰ .N-ob)
        (αᴰ : PshCatIsoᴰ α Pᴰ Qᴰ)
        → PshCatIsoᴰ β Pᴰ Qᴰ
      PshCᴰ-reind-N-ob-Eq-PshIso α≡β α⁻≡β⁻ αᴰ .LocallySmall.CatIsoᴰ.funᴰ =
        PshCᴰ-reind-N-ob-Eq Pᴰ Qᴰ α≡β (αᴰ .LocallySmall.CatIsoᴰ.funᴰ)
      PshCᴰ-reind-N-ob-Eq-PshIso α≡β α⁻≡β⁻ αᴰ .LocallySmall.CatIsoᴰ.invᴰ =
        PshCᴰ-reind-N-ob-Eq Qᴰ Pᴰ α⁻≡β⁻ (αᴰ .LocallySmall.CatIsoᴰ.invᴰ)
      PshCᴰ-reind-N-ob-Eq-PshIso α≡β α⁻≡β⁻ αᴰ .LocallySmall.CatIsoᴰ.secᴰ =
        -- TODO: this is the reason we needed lossy unification. Can maybe avoid if we make the homs of ⊘ no-eta-equality?
        PshCᴰ.⟨ sym $ PshCᴰ-reind-N-ob-Eq-filler Qᴰ Pᴰ _ _ ⟩⋆⟨ sym $ PshCᴰ-reind-N-ob-Eq-filler Pᴰ Qᴰ _ _ ⟩
        ∙ αᴰ .LocallySmall.CatIsoᴰ.secᴰ
      PshCᴰ-reind-N-ob-Eq-PshIso α≡β α⁻≡β⁻ αᴰ .LocallySmall.CatIsoᴰ.retᴰ =
        PshCᴰ.⟨ sym $ PshCᴰ-reind-N-ob-Eq-filler Pᴰ Qᴰ _ _ ⟩⋆⟨ sym $ PshCᴰ-reind-N-ob-Eq-filler Qᴰ Pᴰ _ _ ⟩
        ∙ αᴰ .LocallySmall.CatIsoᴰ.retᴰ

-- TODO: deleted stuff we might want to restore:
-- 1. eqToPshIsoᴰ
-- 2. pathToPshIsoᴰ

-- deleted stuff we might not want to restore:
-- PshHomᴰ→NatTransᴰ and vice-versa
