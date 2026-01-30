{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using (isPshIso' ; PshIso')
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.HLevels
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Functor.More
open import Cubical.Categories.Displayed.BinProduct
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
-- open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.Constructions.BinProduct.More
open import Cubical.Categories.Displayed.Constructions.Graph.Presheaf

open import Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.Base


open Functor
open Iso
open NatIso
open NatTrans
open Categoryᴰ

private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  PshHomStrictN-obTy : Type _
  PshHomStrictN-obTy = ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]

  PshHomStrictN-homTy : PshHomStrictN-obTy → Type _
  PshHomStrictN-homTy N-ob =
    ∀ c c' (f : C [ c , c' ]) (p' : P.p[ c' ]) p →
       (f P.⋆ p') ≡ p
       → f Q.⋆ N-ob c' p' ≡ N-ob c p

  record PshHomStrict : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
    constructor pshhom
    field
      N-ob : PshHomStrictN-obTy
      N-hom : PshHomStrictN-homTy N-ob

  PshHomStrictΣ : Type _
  PshHomStrictΣ = Σ PshHomStrictN-obTy PshHomStrictN-homTy

  isPropN-hom : (N-ob : PshHomStrictN-obTy) →
    isProp (PshHomStrictN-homTy N-ob)
  isPropN-hom N-ob = isPropΠ6 (λ _ _ _ _ _ _ → Q.isSetPsh _ _)

  isSetPshHomStrictΣ : isSet PshHomStrictΣ
  isSetPshHomStrictΣ =
    isSetΣ (isSetΠ (λ _ → isSet→ Q.isSetPsh)) λ _ → isProp→isSet (isPropN-hom _)

  PshHomStrictΣIso : Iso PshHomStrict PshHomStrictΣ
  unquoteDef PshHomStrictΣIso = defineRecordIsoΣ PshHomStrictΣIso (quote (PshHomStrict))

  isSetPshHomStrict : isSet PshHomStrict
  isSetPshHomStrict = isOfHLevelRetractFromIso 2 PshHomStrictΣIso isSetPshHomStrictΣ

open PshHomStrict
module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  makePshHomStrictΣPath : ∀ {α β : PshHomStrictΣ P Q} → α .fst ≡ β .fst
   → α ≡ β
  makePshHomStrictΣPath = ΣPathPProp (isPropN-hom P Q)

  makePshHomStrictPath : ∀ {α β : PshHomStrict P Q} → α .N-ob ≡ β .N-ob
   → α ≡ β
  makePshHomStrictPath {α} {β} N-ob≡ =
    isoFunInjective (PshHomStrictΣIso P Q) α β (makePshHomStrictΣPath N-ob≡)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where

  idPshHomStrict : PshHomStrict P P
  idPshHomStrict .PshHomStrict.N-ob = λ c z → z
  idPshHomStrict .PshHomStrict.N-hom = λ c c' f p' p z → z

module _ {C : Category ℓc ℓc'} where
  module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} where
    _⋆PshHomStrict_ : PshHomStrict P Q → PshHomStrict Q R → PshHomStrict P R
    (α ⋆PshHomStrict β) .N-ob = λ c z → β .N-ob c (α .N-ob c z)
    (α ⋆PshHomStrict β) .N-hom c c' f p' p fp'≡p = β .N-hom c c' f (α .N-ob c' p') (α .N-ob c p)
      (α .N-hom c c' f p' p fp'≡p)
      where
        module P = PresheafNotation P
        module Q = PresheafNotation Q
        module R = PresheafNotation R
    infixr 9 _⋆PshHomStrict_

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  (α : PshHomStrict P Q)
  where
  ⋆PshHomStrictIdL : idPshHomStrict {P = P} ⋆PshHomStrict α ≡ α
  ⋆PshHomStrictIdL = refl
  ⋆PshHomStrictIdR : α ⋆PshHomStrict idPshHomStrict {P = Q}  ≡ α
  ⋆PshHomStrictIdR = refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  {R : Presheaf C ℓr} {S : Presheaf C ℓs}
  (α : PshHomStrict P Q)(β : PshHomStrict Q R)(γ : PshHomStrict R S)
  where

  ⋆PshHomAssoc :
    Path
      (PshHomStrict P S)
      ((α ⋆PshHomStrict β) ⋆PshHomStrict γ)
      (α ⋆PshHomStrict (β ⋆PshHomStrict γ))
  ⋆PshHomAssoc = refl

Unit*Psh-introStrict : ∀ {ℓA} {ℓ1} {C : Category ℓ ℓ'}{P : Presheaf C ℓA}
  → PshHomStrict {ℓq = ℓ1} P Unit*Psh
Unit*Psh-introStrict .N-ob = λ x _ → tt*
Unit*Psh-introStrict .N-hom c c' f p' p x = refl

module _
  {C : Category ℓc ℓc'}
  where
  module _ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
    π₁ : PshHomStrict (P ×Psh Q) P
    π₁ .N-ob _ = fst
    π₁ .N-hom _ _ _ _ _ p≡ = cong fst p≡

    π₂ : PshHomStrict (P ×Psh Q) Q
    π₂ .N-ob _ = snd
    π₂ .N-hom _ _ _ _ _ p≡ = cong snd p≡

  module _
    {P : Presheaf C ℓp}
    {Q : Presheaf C ℓq}
    {R : Presheaf C ℓr}
    (α : PshHomStrict R P)
    (β : PshHomStrict R Q)
    where
    ×PshIntroStrict : PshHomStrict R (P ×Psh Q)
    ×PshIntroStrict .N-ob c x = (α .N-ob c x) , (β .N-ob c x)
    ×PshIntroStrict .N-hom c c' f p r r≡ =
      ΣPathP ((α .N-hom c c' f p r r≡) , (β .N-hom c c' f p r r≡))

    ×Pshβ₁Strict : ×PshIntroStrict ⋆PshHomStrict π₁ P Q ≡ α
    ×Pshβ₁Strict = refl

    ×Pshβ₂Strict : ×PshIntroStrict ⋆PshHomStrict π₂ P Q ≡ β
    ×Pshβ₂Strict = refl

  ΔPshHomStrict : {P : Presheaf C ℓp} → PshHomStrict P (P ×Psh P)
  ΔPshHomStrict = ×PshIntroStrict idPshHomStrict idPshHomStrict

  module _ (P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
    ×PshStrict-UMP : ∀ {R : Presheaf C ℓr} →
      Iso (PshHomStrict R (P ×Psh Q)) (PshHomStrict R P × PshHomStrict R Q)
    ×PshStrict-UMP .Iso.fun α = (α ⋆PshHomStrict π₁ P Q) , (α ⋆PshHomStrict π₂ P Q)
    ×PshStrict-UMP .Iso.inv (α , β) = ×PshIntroStrict α β
    ×PshStrict-UMP .Iso.sec (α , β) = refl
    ×PshStrict-UMP .ret α = refl

open Category
module _ (C : Category ℓC ℓC') (ℓP : Level) where
  PRESHEAF : Category _ _
  PRESHEAF .ob = Presheaf C ℓP
  PRESHEAF .Hom[_,_] = PshHomStrict
  PRESHEAF .id = idPshHomStrict
  PRESHEAF ._⋆_ = _⋆PshHomStrict_
  PRESHEAF .⋆IdL = λ _ → refl
  PRESHEAF .⋆IdR = λ _ → refl
  PRESHEAF .⋆Assoc = λ _ _ _ → refl
  PRESHEAF .isSetHom = isSetPshHomStrict _ _

  open UniversalElementNotation
  Cartesian-PRESHEAF : CartesianCategory _ _
  Cartesian-PRESHEAF .CartesianCategory.C = PRESHEAF
  Cartesian-PRESHEAF .CartesianCategory.term .vertex = Unit*Psh
  Cartesian-PRESHEAF .CartesianCategory.term .element = tt
  Cartesian-PRESHEAF .CartesianCategory.term .universal R =
    isoToIsEquiv
      (iso (λ _ → tt) (λ _ → Unit*Psh-introStrict)
         (λ _ → refl) (λ _ → refl))
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .vertex = P ×Psh Q
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .element =
    (π₁ P Q) , (π₂ P Q)
  Cartesian-PRESHEAF .CartesianCategory.bp (P , Q) .universal R =
    isoToIsEquiv (×PshStrict-UMP P Q)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  PshHetStrict : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHetStrict F P Q = PshHomStrict P (reindPsh F Q)

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {P : Presheaf C ℓP}
  {Q : Presheaf D ℓQ}
  {F : Functor C D}
  (α : PshHetStrict F P Q)
  where
  PshHet→ElementFunctorᴰStrict : Functorᴰ F (RedundElement P) (RedundElement Q)
  PshHet→ElementFunctorᴰStrict =
    mkPropHomsFunctor (hasPropHomsRedundElement Q)
      (λ {x} → α .N-ob x)
      (elimPropBoth (P .F-ob _ .snd)
        (λ _ → isPropPathEq (Q .F-ob (F .F-ob _) .snd))
        (λ p → inl (α .N-hom _ _ _ _ _ p))
        λ where Eq.refl → symPE (Q .F-ob (F .F-ob _) .snd)
                            (inl (sym $ α .N-hom _ _ _ _ _ refl)))

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ D ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf D ℓQ}
  {F : Functor C D}
  where
  _/FᴰStrict_ : (Fᴰ : Functorᴰ F Cᴰ Dᴰ) → (α : PshHetStrict F P Q) → Functor (Cᴰ / P) (Dᴰ / Q)
  Fᴰ /FᴰStrict α = ∫F {F = F} (Fᴰ ×ᴰF PshHet→ElementFunctorᴰStrict α)

module _ {C : Category ℓC ℓC'} {Q : Presheaf C ℓQ} where
  Q→reindPshIdQ : PshHomStrict Q (reindPsh Id Q)
  -- Both of these solved for with auto
  Q→reindPshIdQ .N-ob = λ c z → z
  Q→reindPshIdQ .N-hom = λ c c' f p' p z → z

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}{Dᴰ : Categoryᴰ C ℓDᴰ ℓDᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  where
  module _ (Fᴰ : Functorⱽ Cᴰ Dᴰ) (α : PshHomStrict P Q) where
    _/FⱽStrict_ :  Functor (Cᴰ / P) (Dᴰ / Q)
    _/FⱽStrict_ = Fᴰ /FᴰStrict (α ⋆PshHomStrict Q→reindPshIdQ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
  -- Constructing a fibration from its fibers and restrictions
  _*Strict_ : Presheafᴰ P Cᴰ ℓQᴰ
  _*Strict_ = reindPsh (Idᴰ /FⱽStrict α) Qᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ}
  (α : PshHomStrict P Q)
  (β : PshHomStrict Qᴰ Rᴰ)
  where
  _*StrictF_ : PshHomStrict (α *Strict Qᴰ) (α *Strict Rᴰ)
  _*StrictF_ .N-ob = λ c → β .N-ob (F-ob ((Idᴰ /FⱽStrict α) ^opF) c)
  _*StrictF_ .N-hom = λ c c' f →
                         β .N-hom (F-ob ((Idᴰ /FⱽStrict α) ^opF) c)
                         (F-ob ((Idᴰ /FⱽStrict α) ^opF) c')
                         (F-hom ((Idᴰ /FⱽStrict α) ^opF) f)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  *StrictIdIntro : PshHomStrict Pᴰ (idPshHomStrict *Strict Pᴰ)
  *StrictIdIntro .N-ob = λ c z → z
  *StrictIdIntro .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Pᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

  *StrictIdIntro⁻ : PshHomStrict (idPshHomStrict *Strict Pᴰ) Pᴰ
  *StrictIdIntro⁻ .N-ob = λ c z → z
  *StrictIdIntro⁻ .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Pᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  private
    module Rᴰ = PresheafᴰNotation Rᴰ

  *StrictSeqIntro : PshHomStrict (α *Strict (β *Strict Rᴰ)) ((α ⋆PshHomStrict β) *Strict Rᴰ)
  *StrictSeqIntro .N-ob = λ c z → z
  *StrictSeqIntro .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Rᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

  *StrictSeqIntro⁻ : PshHomStrict ((α ⋆PshHomStrict β) *Strict Rᴰ) (α *Strict (β *Strict Rᴰ))
  *StrictSeqIntro⁻ .N-ob = λ c z → z
  *StrictSeqIntro⁻ .N-hom c c' =
    Hom/-elim λ γ γᴰ →
      elimPropPath
        (P .F-ob (c .fst) .snd)
        (λ _ → isPropΠ3 (λ _ _ _ → Rᴰ.isSetPshᴰ _ _))
        $ λ tri pᴰ' pᴰ γᴰpᴰ'≡pᴰ → γᴰpᴰ'≡pᴰ

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  (Rᴰ : Presheafᴰ Q Cᴰ ℓRᴰ)
  where
  *Strict×ⱽ→×ⱽ*Strict :
    PshHomStrict (α *Strict (Qᴰ ×ⱽPsh Rᴰ)) ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
  *Strict×ⱽ→×ⱽ*Strict = pshhom (λ c z → z) (λ c c' f p' p z → z)

  ×ⱽ*Strict→*Strict×ⱽ :
    PshHomStrict
      ((α *Strict Qᴰ) ×ⱽPsh (α *Strict Rᴰ))
      (α *Strict (Qᴰ ×ⱽPsh Rᴰ))
  ×ⱽ*Strict→*Strict×ⱽ = pshhom (λ c z → z) (λ c c' f p' p z → z)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  PshHomᴰStrict : Type _
  PshHomᴰStrict = PshHomStrict Pᴰ (α *Strict Qᴰ)

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
  idPshHomᴰStrict : PshHomᴰStrict idPshHomStrict Pᴰ Pᴰ
  idPshHomᴰStrict = *StrictIdIntro Pᴰ

module _ {C : Category ℓC ℓC'}{Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  {R : Presheaf C ℓR}
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ}
  {Rᴰ : Presheafᴰ R Cᴰ ℓRᴰ}
  {α : PshHomStrict P Q}
  {β : PshHomStrict Q R}
  where
  private
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ

  _⋆PshHomᴰStrict_ :
    (αᴰ : PshHomᴰStrict α Pᴰ Qᴰ)
    (βᴰ : PshHomᴰStrict β Qᴰ Rᴰ) →
    PshHomᴰStrict (α ⋆PshHomStrict β) Pᴰ Rᴰ
  αᴰ ⋆PshHomᴰStrict βᴰ =
    αᴰ
    ⋆PshHomStrict (α *StrictF βᴰ)
    ⋆PshHomStrict *StrictSeqIntro

  infixr 9 _⋆PshHomᴰStrict_

module _
  (C : Category ℓC ℓC')
  (ℓP ℓPᴰ : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  where
  private
    PSH = PRESHEAF C ℓP
    module PSH = Category PSH
    module Cᴰ = Fibers Cᴰ
  PRESHEAFᴰ : Categoryᴰ (PRESHEAF C ℓP) _ _
  PRESHEAFᴰ .ob[_] P = Presheafᴰ P Cᴰ ℓPᴰ
  PRESHEAFᴰ .Hom[_][_,_] = PshHomᴰStrict
  PRESHEAFᴰ .idᴰ = idPshHomᴰStrict
  PRESHEAFᴰ ._⋆ᴰ_ = _⋆PshHomᴰStrict_
  PRESHEAFᴰ .⋆IdLᴰ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .⋆IdRᴰ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .⋆Assocᴰ _ _ _ = makePshHomStrictPath refl
  PRESHEAFᴰ .isSetHomᴰ = isSetPshHomStrict _ _
  private
    module PSHᴰ = Fibers PRESHEAFᴰ

  PSHᴰTerminalsⱽ : Terminalsⱽ PRESHEAFᴰ
  PSHᴰTerminalsⱽ P .fst = Unit*Psh
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .fun αᴰ = tt
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-ob = λ c _ → tt*
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .inv _ .N-hom = λ _ _ _ _ _ _ → refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .sec _ = refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.isos (Q , Qᴰ , α) .ret _ = makePshHomStrictPath refl
  PSHᴰTerminalsⱽ P .snd .PshIso'.nat _ _ _ _ = inr Eq.refl

  PSHᴰBPⱽ : BinProductsⱽ PRESHEAFᴰ
  PSHᴰBPⱽ Pᴰ Qᴰ =
    UEⱽ→Reprⱽ _ (λ {x = x₁} {y} f → Eq.refl) (record {
        v = Pᴰ ×ⱽPsh Qᴰ
      ; e = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Pᴰ ,
            π₂ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
      ; universal = record {
        nIso = λ c →
          (λ (αᴰ , βᴰ) → ×PshIntroStrict αᴰ βᴰ ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Pᴰ Qᴰ) ,
          (λ _ → ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)) ,
          λ _ → makePshHomStrictPath refl
          } })

  -- Slow, broke
  -- Something about using the record constructor inline vs hiding behind coprojections?
  -- Or is it about more annotations?
  -- PSHᴰFibration : Fibration PRESHEAFᴰ λ f g h → Eq.refl
  -- PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl)
  --   (record {
  --     v = α *Strict Pᴰ
  --   ; e = idPshHomStrict
  --   ; universal = {!!} })

  -- Fast, woke
  PSHᴰFibrationUE : FibrationUE PRESHEAFᴰ (λ f g h → Eq.refl) λ {x} {y} f → Eq.refl
  PSHᴰFibrationUE α Pᴰ .UEⱽ.v = α *Strict Pᴰ
  PSHᴰFibrationUE α Pᴰ .UEⱽ.e = idPshHomStrict
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .fst βᴰ =
    βᴰ ⋆PshHomStrict *StrictSeqIntro⁻
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .fst _ =
    makePshHomStrictPath refl
  PSHᴰFibrationUE α Pᴰ .UEⱽ.universal .isPshIso'.nIso _ .snd .snd _ =
    makePshHomStrictPath refl

  PSHᴰFibration : Fibration PRESHEAFᴰ (λ f g h → Eq.refl)
  PSHᴰFibration α Pᴰ = UEⱽ→Reprⱽ _ (λ {x = x₁} {y = y₁} f → Eq.refl) (PSHᴰFibrationUE α Pᴰ)

  module _ {P : Presheaf C ℓP} (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ

    PSHᴰLRⱽ : LRⱽ PRESHEAFᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
    PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
      where
        module Qᴰ = PresheafᴰNotation Qᴰ

        lrⱽue : UEⱽ
                 ((PRESHEAFᴰ [-][-, Qᴰ ]) ×ⱽPsh
                  reindᴰRedundPshHom
                  (yoRecHom PRESHEAFᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
                  (PRESHEAFᴰ [-][-, Pᴰ ]))
                 (λ {x} {y} f → Eq.refl)
        lrⱽue .UEⱽ.v = Qᴰ ×ⱽPsh (α *Strict Pᴰ)
        lrⱽue .UEⱽ.e .fst = π₁ _ _ ⋆PshHomStrict *StrictIdIntro Qᴰ
        lrⱽue .UEⱽ.e .snd = π₂ _ _
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .fst (αᴰ , βᴰ) =
          ×PshIntroStrict αᴰ βᴰ
          ⋆PshHomStrict ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictSeqIntro⁻)
          ⋆PshHomStrict ×ⱽ*Strict→*Strict×ⱽ (c .snd .snd) Qᴰ (α *Strict Pᴰ)
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .fst _ =
          ΣPathP (makePshHomStrictPath refl , makePshHomStrictPath refl)
        lrⱽue .UEⱽ.universal .isPshIso'.nIso c .snd .snd _ =
          makePshHomStrictPath refl
