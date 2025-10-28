{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation using (NatTrans ; NatIso ; idTrans)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.TotalCategory
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.NaturalTransformation
open import Cubical.Categories.Displayed.NaturalTransformation.More
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.Presheaf.Base

private
  variable
    ℓB ℓB' ℓC ℓC' ℓCᴰ ℓCᴰ' ℓD ℓD' ℓDᴰ ℓDᴰ' ℓP ℓPᴰ ℓQ ℓQᴰ ℓR ℓRᴰ ℓS ℓSᴰ : Level

open Functor
open Functorᴰ
open isIsoᴰ
open isIsoOver
open PshHom
open PshIso

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHom P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  record PshHomᴰ : Type (ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ' $ ℓ-max ℓCᴰ $ ℓ-max ℓC' $ ℓ-max ℓC $ ℓ-max ℓQᴰ $ ℓ-max ℓPᴰ $ ℓ-max ℓP $ ℓ-max ℓCᴰ $ ℓC) where
    no-eta-equality
    field
      N-obᴰ  : ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α .N-ob x p ][ xᴰ ]
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

    N-obᴰ⟨_⟩ :
      ∀ {xxᴰ}{ppᴰ ppᴰ'}
      → Path ∫Pᴰ.p[ xxᴰ ] ppᴰ ppᴰ'
      → Path ∫Qᴰ.p[ xxᴰ ] (_ , N-obᴰ (ppᴰ .snd)) (_ , N-obᴰ (ppᴰ' .snd))
    N-obᴰ⟨_⟩ = cong (∫PshHom .N-ob _)

  isPshIsoᴰ : PshHomᴰ → isPshIso {P = P}{Q = Q} α → Type _
  isPshIsoᴰ αᴰ αIsIso = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
      → isIsoOver (isIsoToIso (αIsIso x)) Pᴰ.p[_][ xᴰ ] Qᴰ.p[_][ xᴰ ]
          (λ _ → αᴰ .PshHomᴰ.N-obᴰ)

  isPshEquivOver : PshHomᴰ → Type _
  isPshEquivOver αᴰ = ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
    → isEquivOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}{f = α .N-ob x}
        λ _ → αᴰ .PshHomᴰ.N-obᴰ

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

  isSetPshHomᴰ : isSet PshHomᴰ
  isSetPshHomᴰ = isOfHLevelRetractFromIso 2 PshHomᴰΣIso isSetPshHomᴰΣ

open PshHomᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P Q : Presheaf C ℓP}
  {α : NatTrans P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  (αᴰ : NatTransᴰ α Pᴰ Qᴰ) where

   NatTransᴰ→PshHomᴰ : PshHomᴰ (NatTrans→PshHom α) Pᴰ Qᴰ
   NatTransᴰ→PshHomᴰ .N-obᴰ = αᴰ .NatTransᴰ.N-obᴰ _ _
   NatTransᴰ→PshHomᴰ .N-homᴰ {p = p} {fᴰ = fᴰ} {pᴰ = pᴰ} =
     funExt₂⁻ (αᴰ .NatTransᴰ.N-homᴰ fᴰ) p pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P Q : Presheaf C ℓP}
  {α : NatTrans P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  (αᴰ : PshHomᴰ (NatTrans→PshHom α) Pᴰ Qᴰ) where
   PshHomᴰ→NatTransᴰ : NatTransᴰ α Pᴰ Qᴰ
   PshHomᴰ→NatTransᴰ .NatTransᴰ.N-obᴰ = λ xᴰ x₁ → αᴰ .N-obᴰ
   PshHomᴰ→NatTransᴰ .NatTransᴰ.N-homᴰ = λ fᴰ → funExt (λ p → funExt (λ pᴰ → αᴰ .N-homᴰ))

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  where

  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P

  module _
    {α β : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ)
    (βᴰ : PshHomᴰ β Pᴰ Qᴰ)
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ

    PshHomᴰPathP : α ≡ β → Type _
    PshHomᴰPathP α≡β = PathP (λ i → PshHomᴰ (α≡β i) Pᴰ Qᴰ) αᴰ βᴰ

    makePshHomᴰPathP :
      (α≡β : α ≡ β) →
      (∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} →
        PathP (λ i → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ α≡β i .N-ob x p ][ xᴰ ])
          (αᴰ .N-obᴰ {x}{xᴰ}{p}) (βᴰ .N-obᴰ)) →
      PshHomᴰPathP α≡β
    makePshHomᴰPathP α≡β αᴰ≡βᴰ i .N-obᴰ = αᴰ≡βᴰ i
    makePshHomᴰPathP α≡β αᴰ≡βᴰ i .N-homᴰ
      {x = x} {y = y} {xᴰ = xᴰ} {f = f} {p = p} {fᴰ = fᴰ} {pᴰ = pᴰ} =
      isSet→SquareP (λ j k → Qᴰ.isSetPshᴰ {p = α≡β j .N-hom x y f p k })
        (αᴰ .N-homᴰ {f = f}{fᴰ = fᴰ}{pᴰ = pᴰ})
        (βᴰ .N-homᴰ {f = f}{fᴰ = fᴰ}{pᴰ = pᴰ})
        (λ j → αᴰ≡βᴰ j (Pᴰ .F-homᴰ fᴰ p pᴰ))
        (λ j → fᴰ Qᴰ.⋆ᴰ αᴰ≡βᴰ j pᴰ)
        i

  module _
    {α : PshHom P Q}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    {αᴰ βᴰ : PshHomᴰ α Pᴰ Qᴰ}
    where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ

    makePshHomᴰPath :
      (∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]} → αᴰ .N-obᴰ {x}{xᴰ}{p} ≡ βᴰ .N-obᴰ)
      → αᴰ ≡ βᴰ
    makePshHomᴰPath = makePshHomᴰPathP _ _ refl


open PshHomᴰ
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  -- TODO make this a record
  PshIsoᴰ : Type _
  PshIsoᴰ =
    Σ[ αᴰ ∈ PshHomᴰ (α .trans) Pᴰ Qᴰ ]
      isPshIsoᴰ (α .trans) Pᴰ Qᴰ αᴰ (α .nIso)
  open IsoOver
  mkPshIsoᴰEquivOver : ∀ (αᴰ : PshHomᴰ (α .trans) Pᴰ Qᴰ)
    → isPshEquivOver (α .trans) Pᴰ Qᴰ αᴰ
    → PshIsoᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .fst = αᴰ
  mkPshIsoᴰEquivOver αᴰ isPshEqv .snd {x}{xᴰ} =
    isisoover (α-isoOver .inv) (α-isoOver .rightInv)
      λ p pᴰ → Pᴰ.rectify $ α-isoOver .leftInv p pᴰ
    where
    α-isoOver = equivOver→IsoOver {P = Pᴰ.p[_][ xᴰ ]}{Q = Qᴰ.p[_][ xᴰ ]}
                  (isoToEquiv (isIsoToIso (α .nIso x)))
      (λ a → αᴰ .PshHomᴰ.N-obᴰ)
      isPshEqv

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  ∫PshIso : PshIsoᴰ α Pᴰ Qᴰ → PshIso (∫P Pᴰ) (∫P Qᴰ)
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .trans = PshHomᴰ.∫PshHom αᴰ
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .fst (q , qᴰ) = _ , αᴰIsPshIsoᴰ .inv q qᴰ
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .snd .fst (q , qᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .rightInv q qᴰ)
  ∫PshIso (αᴰ , αᴰIsPshIsoᴰ) .nIso (x , xᴰ) .snd .snd (p , pᴰ) =
    ΣPathP (_ , αᴰIsPshIsoᴰ .leftInv p pᴰ)

-- Vertical PshHom/Iso are the ones over idPshHom/idPshIso. They need
-- special composition operators to package up the reindexing.
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshHomⱽ : Type _
  PshHomⱽ = PshHomᴰ idPshHom Pᴰ Qᴰ
  PshIsoⱽ : Type _
  PshIsoⱽ = PshIsoᴰ idPshIso Pᴰ Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  (αᴰ : PshHomⱽ Pᴰ Qᴰ) where
  PshHomⱽ→NatTransⱽ : NatTransᴰ (idTrans P) Pᴰ Qᴰ
  PshHomⱽ→NatTransⱽ .NatTransᴰ.N-obᴰ = λ xᴰ x₁ → αᴰ .N-obᴰ
  PshHomⱽ→NatTransⱽ .NatTransᴰ.N-homᴰ = λ fᴰ → funExt (λ p → funExt λ pᴰ → PresheafᴰNotation.rectify Qᴰ (αᴰ .N-homᴰ))

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
  private
    module Cᴰ = Categoryᴰ Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    fun-ty = Eq.singl {A = ∀ {x} → P.p[ x ] → (xᴰ : Cᴰ.ob[ x ]) → Type ℓPᴰ} Pᴰ.p[_][_]
    hom-ty : fun-ty → Type _
    hom-ty singl-fun =
      Eq.singlP (Eq.ap (λ p[_][_] → {x y : Category.ob C}{f : C [ y , x ]} {xᴰ : Cᴰ.ob[ x ]} {yᴰ : Cᴰ.ob[ y ]}
       {p : P.p[ x ]} →
      Cᴰ [ f ][ yᴰ , xᴰ ] → p[ p ][ xᴰ ] → p[ f P.⋆ p ][ yᴰ ]) (singl-fun .snd))
      Pᴰ._⋆ᴰ_
  module _ where
    eqToPshIso-obᴰ : ((p[_][_] , _) : fun-ty) → ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]}
      → Pᴰ.p[ p ][ xᴰ ] → p[ p ][ xᴰ ]
    eqToPshIso-obᴰ (_ , Eq.refl) = λ z → z

    eqToPshIso-invᴰ : ((p[_][_] , _) : fun-ty) → ∀ {x}{xᴰ : Cᴰ.ob[ x ]}{p : P.p[ x ]}
      → p[ p ][ xᴰ ] → Pᴰ.p[ p ][ xᴰ ]
    eqToPshIso-invᴰ (_ , Eq.refl) = λ z → z

    eqToPshIso-homᴰ : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      {x}{y}{xᴰ}{yᴰ}{f : C [ x , y ]}{p : P.p[ y ]} →
      {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]} {pᴰ : Pᴰ.p[ p ][ yᴰ ]}
      → eqToPshIso-obᴰ (p[_][_] , p≡Pp) (fᴰ Pᴰ.⋆ᴰ pᴰ)
        ≡ (fᴰ ⋆ᴰ eqToPshIso-obᴰ (p[_][_] , p≡Pp) pᴰ)
    eqToPshIso-homᴰ (_ , Eq.refl) (_ , Eq.refl) = refl

    eqToPshIso-rightInv : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      → ∀ {x}{xᴰ}{p : P.p[ x ]}{qᴰ : p[ p ][ xᴰ ]}
      → eqToPshIso-obᴰ (p[_][_] , p≡Pp)
      (eqToPshIso-invᴰ (p[_][_] , p≡Pp) qᴰ)
      ≡ qᴰ
    eqToPshIso-rightInv (_ , Eq.refl) (_ , Eq.refl) = refl

    eqToPshIso-leftInv : ∀ ((p[_][_] , p≡Pp) : fun-ty) ((_⋆ᴰ_ , _) : hom-ty (p[_][_] , p≡Pp))
      → ∀ {x}{xᴰ}{p : P.p[ x ]}{pᴰ : Pᴰ.p[ p ][ xᴰ ]}
      → eqToPshIso-invᴰ (p[_][_] , p≡Pp) (eqToPshIso-obᴰ (p[_][_] , p≡Pp) pᴰ)
        ≡ pᴰ
    eqToPshIso-leftInv (_ , Eq.refl) (_ , Eq.refl) = refl

  eqToPshHomⱽ : PresheafᴰEq Pᴰ Qᴰ → PshHomⱽ Pᴰ Qᴰ
  eqToPshHomⱽ Pᴰ≡Qᴰ .N-obᴰ = eqToPshIso-obᴰ (_ , Pᴰ≡Qᴰ .fst)
  eqToPshHomⱽ Pᴰ≡Qᴰ .N-homᴰ = eqToPshIso-homᴰ (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)

  eqToPshIsoⱽ : PresheafᴰEq Pᴰ Qᴰ → PshIsoⱽ Pᴰ Qᴰ
  eqToPshIsoⱽ Pᴰ≡Qᴰ .fst = eqToPshHomⱽ Pᴰ≡Qᴰ
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .inv p = eqToPshIso-invᴰ (_ , Pᴰ≡Qᴰ .fst)
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .rightInv p qᴰ = eqToPshIso-rightInv (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)
  eqToPshIsoⱽ Pᴰ≡Qᴰ .snd .leftInv p pᴰ = eqToPshIso-leftInv (_ , Pᴰ≡Qᴰ .fst) (_ , Pᴰ≡Qᴰ .snd)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  idPshIsoᴰ : PshIsoⱽ Pᴰ Pᴰ
  idPshIsoᴰ = eqToPshIsoⱽ (Eq.refl , Eq.refl)

  idPshHomᴰ : PshHomⱽ Pᴰ Pᴰ
  idPshHomᴰ = idPshIsoᴰ .fst

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
  pathToPshIsoⱽ : Pᴰ ≡ Qᴰ → PshIsoⱽ Pᴰ Qᴰ
  pathToPshIsoⱽ = J (λ Qᴰ _ → PshIsoⱽ Pᴰ Qᴰ) idPshIsoᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ

  module _ {α : PshHom P Q}{β : PshHom Q R} where
    _⋆PshHomᴰ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ) → PshHomᴰ (α ⋆PshHom β) Pᴰ Rᴰ
    (αᴰ ⋆PshHomᴰ βᴰ) = record
      { N-obᴰ = λ pᴰ → ∫⋆ .N-ob _ (_ , pᴰ) .snd
      ; N-homᴰ = Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .N-hom _ _ _ _
      } where
        ∫⋆ = ∫PshHom αᴰ ⋆PshHom ∫PshHom βᴰ

    infixr 9 _⋆PshHomᴰ_

  module _ {α : PshIso P Q}{β : PshIso Q R} where
    _⋆PshIsoᴰ_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)(βᴰ : PshIsoᴰ β Qᴰ Rᴰ) → PshIsoᴰ (α ⋆PshIso β) Pᴰ Rᴰ
    (αᴰ ⋆PshIsoᴰ βᴰ) = (αᴰ .fst ⋆PshHomᴰ βᴰ .fst) ,
      isisoover
        (λ r rᴰ → ∫⋆ .nIso _ .fst (r , rᴰ) .snd)
        (λ r rᴰ → Rᴰ.rectify $ Rᴰ.≡out $ ∫⋆ .nIso _ .snd .fst (r , rᴰ))
        (λ p pᴰ → Pᴰ.rectify $ Pᴰ.≡out $ ∫⋆ .nIso _ .snd .snd (p , pᴰ))
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫⋆ = ∫PshIso αᴰ ⋆PshIso ∫PshIso βᴰ

    infixr 9 _⋆PshIsoᴰ_

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  module _ {α : PshIso P Q} where
    invPshIsoᴰ : PshIsoᴰ α Pᴰ Qᴰ → PshIsoᴰ (invPshIso α) Qᴰ Pᴰ
    invPshIsoᴰ αᴰ = record
      { N-obᴰ = αᴰ .snd .inv _
      ; N-homᴰ = Pᴰ.rectify $ Pᴰ.≡out $ ∫αᴰ⁻ .trans .N-hom _ _ _ _
      }
      , isisoover (λ a → αᴰ .fst .N-obᴰ) (αᴰ .snd .leftInv) (αᴰ .snd .rightInv)
      where
        module Pᴰ = PresheafᴰNotation Pᴰ
        ∫αᴰ⁻ = invPshIso (∫PshIso αᴰ)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}
  where
  invPshIsoⱽ : PshIsoⱽ Pᴰ Qᴰ → PshIsoⱽ Qᴰ Pᴰ
  invPshIsoⱽ αⱽ = record
    { N-obᴰ = αⱽ⁻ .fst .N-obᴰ
    ; N-homᴰ = Pᴰ.rectify $ αⱽ⁻ .fst .N-homᴰ
    } , (isisoover
      (αⱽ⁻ .snd .inv)
      (αⱽ⁻ .snd .rightInv)
      (αⱽ⁻ .snd .leftInv))
    where
      module Pᴰ = PresheafᴰNotation Pᴰ
      αⱽ⁻ = invPshIsoᴰ αⱽ

-- The variants of these are all just eta expansions. We could do
-- something like reindF' but I'll just copy/paste for today.
module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  _⋆PshHomⱽ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomⱽ Pᴰ Rᴰ
  αᴰ ⋆PshHomⱽ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
    where
      αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ

  _⋆PshIsoⱽ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoⱽ Pᴰ Rᴰ
  αᴰ ⋆PshIsoⱽ βᴰ = (αᴰ .fst ⋆PshHomⱽ βᴰ .fst)
    , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                 (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                 (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
    where
      αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ
  infixr 9 _⋆PshHomⱽ_
  infixr 9 _⋆PshIsoⱽ_

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  module _ {α : PshHom P Q} where
    _⋆PshHomᴰⱽ_ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ) → PshHomᴰ α Pᴰ Rᴰ
    αᴰ ⋆PshHomᴰⱽ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ
    infixr 9 _⋆PshHomᴰⱽ_


  module _ {α : PshIso P Q} where
    _⋆PshIsoᴰⱽ_ : (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)(βᴰ : PshIsoⱽ Qᴰ Rᴰ) → PshIsoᴰ α Pᴰ Rᴰ
    αᴰ ⋆PshIsoᴰⱽ βᴰ = (αᴰ .fst ⋆PshHomᴰⱽ βᴰ .fst)
      , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                   (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                   (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ
    infixr 9 _⋆PshIsoᴰⱽ_


module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  module _ {β : PshHom P R} where
    _⋆PshHomⱽᴰ_ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ) → PshHomᴰ β Pᴰ Rᴰ
    αᴰ ⋆PshHomⱽᴰ βᴰ = record { N-obᴰ = αᴰ⋆ᴰβᴰ .N-obᴰ ; N-homᴰ = Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .N-homᴰ }
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshHomᴰ βᴰ

  module _ {β : PshIso P R} where
    _⋆PshIsoⱽᴰ_ : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)(βᴰ : PshIsoᴰ β Qᴰ Rᴰ) → PshIsoᴰ β Pᴰ Rᴰ
    αᴰ ⋆PshIsoⱽᴰ βᴰ = (αᴰ .fst ⋆PshHomⱽᴰ βᴰ .fst)
      , (isisoover (αᴰ⋆ᴰβᴰ .snd .inv)
                   (λ _ _ → Rᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .rightInv _ _)
                   (λ _ _ → Pᴰ.rectify $ αᴰ⋆ᴰβᴰ .snd .leftInv _ _))
      where
        αᴰ⋆ᴰβᴰ = αᴰ ⋆PshIsoᴰ βᴰ
    infixr 9 _⋆PshIsoⱽᴰ_

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where
  ⋆PshHomIdLⱽᴰ : (αᴰ : PshHomᴰ α Pᴰ Qᴰ) → idPshHomᴰ ⋆PshHomⱽᴰ αᴰ ≡ αᴰ
  ⋆PshHomIdLⱽᴰ αᴰ = makePshHomᴰPath refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{S : Presheaf C ℓS}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ}{Sᴰ : Presheafᴰ S Cᴰ ℓSᴰ}
  {γ : PshHom P S} where
  ⋆PshHomAssocⱽⱽᴰ : (αᴰ : PshHomⱽ Pᴰ Qᴰ)(βᴰ : PshHomⱽ Qᴰ Rᴰ)(γᴰ : PshHomᴰ γ Rᴰ Sᴰ)
    → (αᴰ ⋆PshHomⱽ βᴰ) ⋆PshHomⱽᴰ γᴰ ≡ αᴰ ⋆PshHomⱽᴰ (βᴰ ⋆PshHomⱽᴰ γᴰ)
  ⋆PshHomAssocⱽⱽᴰ αᴰ βᴰ γᴰ = makePshHomᴰPath refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ) where
  PshIsoⱽ' : Type _
  PshIsoⱽ' =
    Σ[ α ∈ PshHomⱽ Pᴰ Qᴰ ]
    Σ[ α⁻ ∈ PshHomⱽ Qᴰ Pᴰ ]
    (α ⋆PshHomⱽ α⁻ ≡ idPshHomᴰ)
    × (α⁻ ⋆PshHomⱽ α ≡ idPshHomᴰ)

  PshIsoⱽ'→PshIsoⱽ : PshIsoⱽ' → PshIsoⱽ Pᴰ Qᴰ
  PshIsoⱽ'→PshIsoⱽ (α , α⁻ , αα⁻ , α⁻α) .fst = α
  PshIsoⱽ'→PshIsoⱽ (α , α⁻ , αα⁻ , α⁻α) .snd .inv = λ a → α⁻ .N-obᴰ
  PshIsoⱽ'→PshIsoⱽ (α , α⁻ , αα⁻ , α⁻α) .snd .rightInv _ q i = α⁻α i .N-obᴰ q
  PshIsoⱽ'→PshIsoⱽ (α , α⁻ , αα⁻ , α⁻α) .snd .leftInv _ q i = αα⁻ i .N-obᴰ q

  PshIsoⱽ→PshIsoⱽ' : PshIsoⱽ Pᴰ Qᴰ → PshIsoⱽ'
  PshIsoⱽ→PshIsoⱽ' αⱽ .fst = αⱽ .fst
  PshIsoⱽ→PshIsoⱽ' αⱽ .snd .fst = invPshIsoⱽ αⱽ .fst
  PshIsoⱽ→PshIsoⱽ' αⱽ .snd .snd .fst = makePshHomᴰPath (funExt λ p → αⱽ .snd .leftInv _ p)
  PshIsoⱽ→PshIsoⱽ' αⱽ .snd .snd .snd = makePshHomᴰPath (funExt λ q → αⱽ .snd .rightInv _ q)

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}{Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ}{Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ
  precomp⋆PshHomⱽᴰ-Iso
    : (αᴰ : PshIsoⱽ Pᴰ Qᴰ)
    → ∀ {β : PshHom P R}
    → Iso (PshHomᴰ β Qᴰ Rᴰ) (PshHomᴰ β Pᴰ Rᴰ)
  precomp⋆PshHomⱽᴰ-Iso αᴰ .Iso.fun βᴰ = αᴰ .fst ⋆PshHomⱽᴰ βᴰ
  precomp⋆PshHomⱽᴰ-Iso αᴰ .Iso.inv βᴰ = invPshIsoⱽ αᴰ .fst ⋆PshHomⱽᴰ βᴰ
  precomp⋆PshHomⱽᴰ-Iso αᴰ .Iso.rightInv βᴰ =
    sym (⋆PshHomAssocⱽⱽᴰ _ _ _)
    ∙ cong (_⋆PshHomⱽᴰ βᴰ) (PshIsoⱽ→PshIsoⱽ' _ _ αᴰ .snd .snd .fst)
    ∙ ⋆PshHomIdLⱽᴰ βᴰ
  precomp⋆PshHomⱽᴰ-Iso αᴰ .Iso.leftInv βᴰ = sym (⋆PshHomAssocⱽⱽᴰ _ _ _)
    ∙ cong (_⋆PshHomⱽᴰ βᴰ) (PshIsoⱽ→PshIsoⱽ' _ _ αᴰ .snd .snd .snd)
    ∙ ⋆PshHomIdLⱽᴰ βᴰ

-- We can use paths if the presheaves are of the same level
module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓP}
  (α : PshIso P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ) where
  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
  module _ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) {x : C.ob} where
    private
      α⟨x⟩ : CatIso (SET ℓP) (P .F-ob x) (Q .F-ob x)
      α⟨x⟩ = PshIso→SETIso P Q α x
    PshIsoᴰ→SETᴰIsoᴰ : ∀ xᴰ → CatIsoᴰ (SETᴰ ℓP ℓPᴰ) α⟨x⟩ (Pᴰ .F-obᴰ xᴰ) (Qᴰ .F-obᴰ xᴰ)
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .fst p pᴰ = αᴰ .fst .N-obᴰ pᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .invᴰ q qᴰ = αᴰ .snd .inv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .secᴰ = funExt λ q → funExt λ qᴰ →
      αᴰ .snd .rightInv q qᴰ
    PshIsoᴰ→SETᴰIsoᴰ xᴰ .snd .retᴰ = funExt λ p → funExt λ pᴰ →
      αᴰ .snd .leftInv p pᴰ

  PshIsoᴰ→PathP
      : ∀ (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
      → PathP (λ i → Presheafᴰ (PshIso→Path P Q α i) Cᴰ ℓPᴰ) Pᴰ Qᴰ
  PshIsoᴰ→PathP αᴰ =
    Functorᴰ≡
      (λ xᴰ → CatIsoᴰ→P≡Q (PshIso→SETIso P Q α _) (PshIsoᴰ→SETᴰIsoᴰ αᴰ xᴰ))
      λ {x = x}{xᴰ = xᴰ} fᴰ →
        toPathP (funExt (λ q → funExt (λ qᴰ → Qᴰ.rectify $ Qᴰ.≡out $
          sym (Qᴰ.reind-filler _ _)
          ∙ cong (∫αᴰ .trans .N-ob _) Pᴰ.⟨ refl ⟩⋆⟨ (sym $ Pᴰ.reind-filler _ _) ⟩
          ∙ ∫αᴰ .trans .N-hom _ _ _ _
          ∙ Qᴰ.⟨ refl ⟩⋆⟨ cong (∫αᴰ .trans .N-ob _) (cong (∫αᴰ .nIso _ .fst) (sym $ Qᴰ.reind-filler _ _))
                 ∙ ∫αᴰ .nIso _ .snd .fst _ ⟩
        )))
    where
      ∫αᴰ : PshIso (∫P Pᴰ) (∫P Qᴰ)
      ∫αᴰ = ∫PshIso αᴰ

module _
  {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {D : Category ℓD ℓD'}
  {Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf D ℓP}
  {Pᴰ : Presheafᴰ P Dᴰ ℓPᴰ}
  {Q : Presheaf D ℓQ}
  {Qᴰ : Presheafᴰ Q Dᴰ ℓQᴰ}
  where
  _∘ˡᴰ_ : ∀ {α : PshHom P Q} {F : Functor C D}
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → PshHomᴰ (α ∘ˡ F) (Pᴰ ∘Fᴰ (Fᴰ ^opFᴰ)) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
  (αᴰ ∘ˡᴰ Fᴰ) .N-obᴰ = αᴰ .N-obᴰ
  (αᴰ ∘ˡᴰ Fᴰ) .N-homᴰ = αᴰ .N-homᴰ

  _∘ˡⁱᴰ_ : ∀ {α : PshIso P Q} {F : Functor C D}
    (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) (Fᴰ : Functorᴰ F Cᴰ Dᴰ)
    → PshIsoᴰ (α ∘ˡⁱ F) (Pᴰ ∘Fᴰ (Fᴰ ^opFᴰ)) (Qᴰ ∘Fᴰ (Fᴰ ^opFᴰ))
  (αᴰ ∘ˡⁱᴰ Fᴰ) .fst = αᴰ .fst ∘ˡᴰ Fᴰ
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .inv = αᴰ .snd .inv
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .rightInv = αᴰ .snd .rightInv
  (αᴰ ∘ˡⁱᴰ Fᴰ) .snd .leftInv = αᴰ .snd .leftInv

  -- TODO: whiskering for universal element

module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshHom P Q}
  where

  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  αβ-N-ob-ty = Eq.singl (α .N-ob)

  module _
    {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
    {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
    {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
    (αᴰ : PshHomᴰ α Pᴰ Qᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      module Cᴰ = Categoryᴰ Cᴰ
      module Qᴰ = PresheafᴰNotation Qᴰ

    PshHomEqPshHomᴰ-N-obᴰ :
      (αβ-N-ob : αβ-N-ob-ty) →
        ∀ {x}{xᴰ : Cᴰ.ob[ x ]}
        {p : P.p[ x ]} → Pᴰ.p[ p ][ xᴰ ] → Qᴰ.p[ αβ-N-ob .fst x p ][ xᴰ ]
    PshHomEqPshHomᴰ-N-obᴰ (_ , Eq.refl) = αᴰ .N-obᴰ

    opaque
      PshHomEqPshHomᴰ-N-hom :
        (αβ-N-ob : αβ-N-ob-ty) →
        ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
          αβ-N-ob .fst c (f P.⋆ p) ≡ (f Q.⋆ αβ-N-ob .fst c' p)
      PshHomEqPshHomᴰ-N-hom (_ , Eq.refl) c c' f p = α .N-hom c c' f p

      PshHomEqPshHomᴰ-N-homᴰ :
        (αβ-N-ob : αβ-N-ob-ty) →
          ∀ {x y}{xᴰ : Cᴰ.ob[ x ]}{yᴰ : Cᴰ.ob[ y ]}
          → {f : C [ x , y ]}{p : P.p[ y ]}
          → {fᴰ : Cᴰ [ f ][ xᴰ , yᴰ ]}{pᴰ : Pᴰ.p[ p ][ yᴰ ]}
          → PshHomEqPshHomᴰ-N-obᴰ αβ-N-ob (fᴰ Pᴰ.⋆ᴰ pᴰ)
              Qᴰ.≡[ PshHomEqPshHomᴰ-N-hom αβ-N-ob x y f p ]
              (fᴰ Qᴰ.⋆ᴰ PshHomEqPshHomᴰ-N-obᴰ αβ-N-ob pᴰ)
      PshHomEqPshHomᴰ-N-homᴰ (_ , Eq.refl) = αᴰ .N-homᴰ

    module _ {β : PshHom P Q} where
      module _
        (eq-N-ob : α .N-ob Eq.≡ β .N-ob)
        where
        -- Change the base PshHom of a PshHomᴰ along
        -- an equality (Eq.≡) of PshHoms
        PshHomEqPshHomᴰ : PshHomᴰ β Pᴰ Qᴰ
        PshHomEqPshHomᴰ .N-obᴰ =
          PshHomEqPshHomᴰ-N-obᴰ (_ , eq-N-ob)
        PshHomEqPshHomᴰ .N-homᴰ =
          Qᴰ.rectify (PshHomEqPshHomᴰ-N-homᴰ (_ , eq-N-ob))

      module _ (α≡β : α ≡ β) where

        -- Change the base PshHom of a PshHomᴰ along
        -- a path of PshHoms
        PshHomPathPshHomᴰ : PshHomᴰ β Pᴰ Qᴰ
        PshHomPathPshHomᴰ .N-obᴰ {x = x} {p = p} pᴰ =
          Qᴰ.reind (funExt₂⁻ (λ i → α≡β i .N-ob) x p) $
            αᴰ .N-obᴰ pᴰ
        PshHomPathPshHomᴰ .N-homᴰ =
          Qᴰ.rectify $ Qᴰ.≡out $
            (sym $ Qᴰ.reind-filler _ _)
            ∙ Qᴰ.≡in (αᴰ .N-homᴰ)
            ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ _ ⟩

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  where

  private
    module C = Category C
    module Cᴰ = Categoryᴰ Cᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  module _ {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} (αᴰ : PshIsoᴰ α Pᴰ Qᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ
      PshHomEqPshIsoᴰ-isPshIso :
        (αβ-N-ob : αβ-N-ob-ty {α = α .trans}) →
        ∀ x → Σ[ g ∈ (Q.p[ x ] → P.p[ x ]) ]
              Σ[ _ ∈ section (αβ-N-ob .fst x) g ]
              retract (αβ-N-ob .fst x) g
      PshHomEqPshIsoᴰ-isPshIso (_ , Eq.refl) = α .nIso

      PshHomEqPshIsoᴰ-isPshIsoᴰ :
        (αβ-N-ob : αβ-N-ob-ty {α = α .trans}) →
          ∀ {x}{xᴰ : Cᴰ.ob[ x ]} →
          isIsoOver
            (isIsoToIso (PshHomEqPshIsoᴰ-isPshIso αβ-N-ob x))
            Pᴰ.p[_][ xᴰ ]
            Qᴰ.p[_][ xᴰ ]
            (λ _ → PshHomEqPshHomᴰ-N-obᴰ (αᴰ .fst) αβ-N-ob)
      PshHomEqPshIsoᴰ-isPshIsoᴰ (_ , Eq.refl) = αᴰ .snd

    module _ {β : PshIso P Q} (eq-N-ob : α .trans .N-ob Eq.≡ β .trans .N-ob) where
      private
        opaque
          isPshIso≡ :
            PshHomEqPshIsoᴰ-isPshIso (_ , eq-N-ob) ≡ β .nIso
          isPshIso≡  =
              isPropIsPshIso {α = β .trans}
                (PshHomEqPshIsoᴰ-isPshIso (_ , eq-N-ob)) (β .nIso)

      PshHomEqPshIsoᴰ : PshIsoᴰ β Pᴰ Qᴰ
      PshHomEqPshIsoᴰ .fst = PshHomEqPshHomᴰ (αᴰ .fst) eq-N-ob
      PshHomEqPshIsoᴰ .snd =
        subst
          (λ z → isIsoOver
            (isIsoToIso z)
            Pᴰ.p[_][ _ ] Qᴰ.p[_][ _ ]
            λ _ → PshHomEqPshHomᴰ-N-obᴰ (αᴰ .fst) (_ , eq-N-ob))
          (funExt⁻ isPshIso≡ _)
          (PshHomEqPshIsoᴰ-isPshIsoᴰ (_ , eq-N-ob))

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  where

  module _ {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} where
    -- TODO I don't know what the right eq-based lemma I need
    -- to generalize this
    precomp𝟙ᴰPshIsoᴰ :
      PshIsoᴰ (precomp𝟙PshIso P) Pᴰ (Pᴰ ∘Fᴰ (𝟙ᴰ⟨ Cᴰ ⟩ ^opFᴰ))
    precomp𝟙ᴰPshIsoᴰ .fst .N-obᴰ = λ z → z
    precomp𝟙ᴰPshIsoᴰ .fst .N-homᴰ = refl
    precomp𝟙ᴰPshIsoᴰ .snd .inv = λ _ z → z
    precomp𝟙ᴰPshIsoᴰ .snd .rightInv _ _ = refl
    precomp𝟙ᴰPshIsoᴰ .snd .leftInv _ _ = refl

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P Q : Presheaf C ℓP}
  {α : NatIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓPᴰ}
  (αᴰ : NatIsoᴰ α Pᴰ Qᴰ) where

   NatIsoᴰ→PshIsoᴰ :
     PshIsoᴰ
       (NatIso→PshIso P Q α)
       Pᴰ Qᴰ
   NatIsoᴰ→PshIsoᴰ .fst = NatTransᴰ→PshHomᴰ (αᴰ .NatIsoᴰ.transᴰ)
   NatIsoᴰ→PshIsoᴰ .snd .inv = αᴰ .NatIsoᴰ.nIsoᴰ _ .invᴰ
   NatIsoᴰ→PshIsoᴰ .snd .rightInv b q i =
     αᴰ .NatIsoᴰ.nIsoᴰ _ .secᴰ i b q
   NatIsoᴰ→PshIsoᴰ .snd .leftInv a p i =
     αᴰ .NatIsoᴰ.nIsoᴰ _ .retᴰ i a p

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR} {S : Presheaf C ℓS}
  {α : PshHom P Q}{β : PshHom Q R}{γ : PshHom R S}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ} {Sᴰ : Presheafᴰ S Cᴰ ℓSᴰ}
  (αᴰ : PshHomᴰ α Pᴰ Qᴰ)(βᴰ : PshHomᴰ β Qᴰ Rᴰ)(γᴰ : PshHomᴰ γ Rᴰ Sᴰ)
  where

  private
    module Sᴰ = PresheafᴰNotation Sᴰ

  ⋆PshHomᴰAssoc :
    PshHomᴰPathP
      ((αᴰ ⋆PshHomᴰ βᴰ) ⋆PshHomᴰ γᴰ)
      (αᴰ ⋆PshHomᴰ βᴰ ⋆PshHomᴰ γᴰ)
      (⋆PshHomAssoc α β γ)
  ⋆PshHomᴰAssoc =
    makePshHomᴰPathP _ _ _
      λ {x}{xᴰ}{p} → funExt λ pᴰ →
        Sᴰ.rectify {p = refl} refl

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  {α : PshIso P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  (αᴰ : PshIsoᴰ α Pᴰ Qᴰ)
  where

  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  PshIsoᴰ→leftInvᴰ :
    PshHomᴰPathP (αᴰ .fst ⋆PshHomᴰ invPshIsoᴰ αᴰ .fst) idPshHomᴰ (PshIso→leftInv α)
  PshIsoᴰ→leftInvᴰ =
    makePshHomᴰPathP _ _ _ λ {x}{xᴰ}{p} → funExt λ pᴰ →
      Pᴰ.rectify (αᴰ .snd .leftInv p pᴰ)

  PshIsoᴰ→rightInvᴰ :
    PshHomᴰPathP (invPshIsoᴰ αᴰ .fst ⋆PshHomᴰ αᴰ .fst) idPshHomᴰ (PshIso→rightInv α)
  PshIsoᴰ→rightInvᴰ =
    makePshHomᴰPathP _ _ _ λ {x}{xᴰ}{q} → funExt λ qᴰ →
      Qᴰ.rectify (αᴰ .snd .rightInv q qᴰ)

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  {α β : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {αᴰ : PshHomᴰ α Pᴰ Qᴰ}
  {βᴰ : PshHomᴰ β Pᴰ Qᴰ}
  {α≡β α≡β' : α ≡ β}
  where

   private
     module Qᴰ = PresheafᴰNotation Qᴰ

   PshHomᴰPathP-rectify :
     PshHomᴰPathP αᴰ βᴰ α≡β →
     PshHomᴰPathP αᴰ βᴰ α≡β'
   PshHomᴰPathP-rectify ϕᴰ =
     makePshHomᴰPathP αᴰ βᴰ α≡β' λ {x}{xᴰ}{p} → funExt λ pᴰ →
       Qᴰ.rectify (congP (λ i u → u .N-obᴰ pᴰ) ϕᴰ)

module _
  {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  {α β γ : PshHom P Q}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ} {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {αᴰ : PshHomᴰ α Pᴰ Qᴰ}
  {βᴰ : PshHomᴰ β Pᴰ Qᴰ}
  {γᴰ : PshHomᴰ γ Pᴰ Qᴰ}
  {α≡β : α ≡ β}
  {β≡γ : β ≡ γ}
  where

  compPshHomᴰPathP :
    PshHomᴰPathP αᴰ βᴰ α≡β →
    PshHomᴰPathP βᴰ γᴰ β≡γ →
    PshHomᴰPathP αᴰ γᴰ (α≡β ∙ β≡γ)
  compPshHomᴰPathP ϕᴰ ψᴰ i =
    -- Don't even ask
    -- I couldn't figure out the right cubical bit of the
    -- library to make this work, but somehow hacked this together
    -- It's like some amalgamation of congP and compPathP
    comp (λ j → PshHomᴰ (compPath-filler α≡β β≡γ j i) Pᴰ Qᴰ)
      (λ j → λ { (i = i0) → αᴰ ; (i = i1) → ψᴰ j})
      (ϕᴰ i)

  module _ {α≡γ : α ≡ γ} where
    compPshHomᴰPathP' :
      PshHomᴰPathP αᴰ βᴰ α≡β →
      PshHomᴰPathP βᴰ γᴰ β≡γ →
      PshHomᴰPathP αᴰ γᴰ α≡γ
    compPshHomᴰPathP' ϕᴰ ψᴰ = PshHomᴰPathP-rectify (compPshHomᴰPathP ϕᴰ ψᴰ)
