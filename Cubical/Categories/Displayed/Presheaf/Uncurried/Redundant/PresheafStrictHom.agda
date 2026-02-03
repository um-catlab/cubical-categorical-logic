{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Displayed.Presheaf.Uncurried.Redundant.PresheafStrictHom where
-- TODO still need better name

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq

open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Fiber
open import Cubical.Categories.Constructions.TotalCategory.Base
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.HLevels
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Props
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Exponentials
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt using
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
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
-- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions renaming
--   (push to pushPsh)
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

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  isPshIsoStrict : PshHomStrict P Q → Type _
  isPshIsoStrict α = ∀ x → isIso (α .N-ob x)

  isPropIsPshIsoStrict : ∀ {α} → isProp (isPshIsoStrict α)
  isPropIsPshIsoStrict = isPropΠ λ _ → isPropIsIsoSet (P .F-ob _ .snd) (Q .F-ob _ .snd)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  record PshIsoStrict : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    constructor pshiso
    field
      trans : PshHomStrict P Q
      nIso : isPshIsoStrict {P = P}{Q = Q} trans

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq}
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  invPshIsoStrict : (α : PshIsoStrict P Q) → PshIsoStrict Q P
  invPshIsoStrict α = pshiso invTrans invNIso
    where
      open PshIsoStrict α renaming (nIso to αnIso ; trans to αtrans)
      inv' : ∀ c → Q.p[ c ] → P.p[ c ]
      inv' c = αnIso c .fst

      sec' : ∀ c q → αtrans .N-ob c (inv' c q) ≡ q
      sec' c = αnIso c .snd .fst

      ret' : ∀ c p → inv' c (αtrans .N-ob c p) ≡ p
      ret' c = αnIso c .snd .snd

      invTrans : PshHomStrict Q P
      invTrans .N-ob = inv'
      invTrans .N-hom c c' f q' q eq =
        isoFunInjective (iso (αtrans .N-ob c) (inv' c) (sec' c) (ret' c)) _ _
          (sym (αtrans .N-hom c c' f (inv' c' q') (f P.⋆ inv' c' q') refl)
           ∙ cong (f Q.⋆_) (sec' c' q')
           ∙ eq
           ∙ sym (sec' c q))

      invNIso : isPshIsoStrict {P = Q}{Q = P} invTrans
      invNIso x = αtrans .N-ob x , ret' x , sec' x

  -- Convenient when we already have the iso on Types
  Isos→PshIsoStrict : (isos : ∀ x → Iso (P.p[ x ]) (Q.p[ x ]))
    → (∀ x y (f : C [ x , y ]) (p : P.p[ y ]) →
        fun (isos x) (f P.⋆ p) ≡ f Q.⋆ (fun (isos y) p))
    → PshIsoStrict P Q
  Isos→PshIsoStrict isos isos-areNat = pshiso theTrans theNIso
    where
      theTrans : PshHomStrict P Q
      theTrans .N-ob x = fun (isos x)
      theTrans .N-hom c c' f p' p eq =
        sym (isos-areNat c c' f p') ∙ cong (fun (isos c)) eq

      theNIso : isPshIsoStrict theTrans
      theNIso x = inv (isos x) , sec (isos x) , ret (isos x)

-- module _
--   {C : Category ℓc ℓc'}
--   {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
--   where

--   module _ (α : PshHom P Q) where
--     PshHom→PshHomStrict : PshHomStrict P Q
--     PshHom→PshHomStrict .N-ob = α .PshHom.N-ob
--     PshHom→PshHomStrict .N-hom c c' f p p' e =
--       sym (α .PshHom.N-hom _ _ f p) ∙ cong (α .PshHom.N-ob c) e

--   module _ (α : PshHomStrict P Q) where
--     PshHomStrict→PshHom : PshHom P Q
--     PshHomStrict→PshHom .PshHom.N-ob = α .N-ob
--     PshHomStrict→PshHom .PshHom.N-hom c c' f p = sym $ α .N-hom c c' f p (P .F-hom f p) refl

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

module _ {C : Category ℓC ℓC'} where
  PshHomStrictPsh :
    ∀ (Q : Presheaf C ℓQ) →
        Presheaf (PRESHEAF C ℓP) (ℓC ⊔ℓ ℓC' ⊔ℓ ℓQ ⊔ℓ ℓP)
  PshHomStrictPsh Q .F-ob P = (PshHomStrict P Q) , (isSetPshHomStrict _ _)
  PshHomStrictPsh Q .F-hom = _⋆PshHomStrict_
  PshHomStrictPsh Q .F-id = funExt (λ _ → makePshHomStrictPath refl)
  PshHomStrictPsh Q .F-seq α α' = funExt λ _ → makePshHomStrictPath refl

module _ {C : Category ℓ ℓ'} where
  open Functor
  private
    module C = Category C

  YOStrict : Functor C (PRESHEAF C ℓ')
  YOStrict .F-ob = yo
  YOStrict .F-hom f .N-ob c g = g C.⋆ f
  YOStrict .F-hom f .N-hom c c' g p' p e = (sym $ C.⋆Assoc _ _ _) ∙ cong₂ C._⋆_ e refl
  YOStrict .F-id = makePshHomStrictPath (funExt₂ λ _ _ → C.⋆IdR _)
  YOStrict .F-seq _ _ = makePshHomStrictPath (funExt₂ λ _ _ → sym $ C.⋆Assoc _ _ _)

-- module _ {C : Category ℓ ℓ'} where
--   private
--     module C = Category C
--   PshProd' : Functor
--     (PresheafCategory C ℓA ×C PresheafCategory C ℓB)
--     (PresheafCategory C (ℓ-max ℓA ℓB))
--   PshProd' = (postcomposeF _ ×Sets ∘F ,F-functor)

--   PshProd : Bifunctor (PresheafCategory C ℓA) (PresheafCategory C ℓB)
--                       (PresheafCategory C (ℓ-max ℓA ℓB))
--   PshProd = ParFunctorToBifunctor PshProd'

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
  _⇒PshLargeStrict_ : Presheaf C (ℓC ⊔ℓ ℓQ ⊔ℓ ℓC' ⊔ℓ ℓP)
  _⇒PshLargeStrict_ = PshHomStrictPsh Q ∘F ((-×P ∘F YOStrict) ^opF)
    where
    -×P : Functor (PRESHEAF C ℓC') (PRESHEAF C (ℓC' ⊔ℓ ℓP))
    -×P .F-ob R = R ×Psh P
    -×P .F-hom α = ×PshIntroStrict (π₁ _ _ ⋆PshHomStrict α) (π₂ _ _)
    -×P .F-id = makePshHomStrictPath refl
    -×P .F-seq _ _ = makePshHomStrictPath refl

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) (Q : Presheaf C ℓQ) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  appPshHomStrict : PshHomStrict ((P ⇒PshLargeStrict Q) ×Psh P) Q
  appPshHomStrict .N-ob c (α , p) = α .N-ob c (C.id , p)
  appPshHomStrict .N-hom c c' f (α , p) (β , p') e =
    α .N-hom c c' f (C.id , p) (f , f P.⋆ p) (ΣPathP (C.⋆IdR f , refl))
    ∙ cong (λ x → α .N-ob c (x , f P.⋆ p)) (sym (C.⋆IdL f))
    ∙ cong (λ γ → γ .N-ob c (C.id , f P.⋆ p)) (cong fst e)
    ∙ cong (λ x → β .N-ob c (C.id , x)) (cong snd e)

  module _ {R : Presheaf C ℓR} where
    private
      module R = PresheafNotation R

    λPshHomStrict : PshHomStrict (R ×Psh P) Q → PshHomStrict R (P ⇒PshLargeStrict Q)
    λPshHomStrict γ .N-ob c r .N-ob d (f , p) = γ .N-ob d (f R.⋆ r , p)
    λPshHomStrict γ .N-ob c r .N-hom e d g (f' , p') (f , p) eq =
      γ .N-hom e d g (f' R.⋆ r , p') (f R.⋆ r , p)
        (ΣPathP ((sym $ R.⋆Assoc _ _ _) ∙ R.⟨ cong fst eq ⟩⋆⟨⟩ , cong snd eq))
    λPshHomStrict γ .N-hom d c' h s' s eq =
      makePshHomStrictPath
      (funExt₂ λ e (f , p) →
        cong (λ x → γ .N-ob e (x , p))
          (R.⋆Assoc _ _ _ ∙ R.⟨⟩⋆⟨ eq ⟩))

    ⇒PshLargeStrict-UMP : Iso (PshHomStrict R (P ⇒PshLargeStrict Q))
                              (PshHomStrict (R ×Psh P) Q)
    ⇒PshLargeStrict-UMP .Iso.fun α =
      ×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P) ⋆PshHomStrict appPshHomStrict
    ⇒PshLargeStrict-UMP .Iso.inv = λPshHomStrict
    ⇒PshLargeStrict-UMP .Iso.sec γ = makePshHomStrictPath
      (funExt₂ λ c (r , p) → cong (λ x → γ .N-ob c (x , p)) (R.⋆IdL r))
    ⇒PshLargeStrict-UMP .Iso.ret α = makePshHomStrictPath
      (funExt₂ λ c r → makePshHomStrictPath
        (funExt₂ λ d (f , p) →
          sym (cong (λ x → α .N-ob c r .N-ob d (x , p)) (sym (C.⋆IdL f))
          ∙ funExt⁻ (funExt⁻ (cong N-ob (α .N-hom d c f r (f R.⋆ r) refl)) d) (C.id , p))))

    ⇒PshLargeStrict-β : (γ : PshHomStrict (R ×Psh P) Q) →
      ×PshIntroStrict (π₁ R P ⋆PshHomStrict λPshHomStrict γ) (π₂ R P) ⋆PshHomStrict appPshHomStrict
        ≡ γ
    ⇒PshLargeStrict-β γ = makePshHomStrictPath
      (funExt₂ λ c (r , p) → cong (λ x → γ .N-ob c (x , p)) (R.⋆IdL r))

    ⇒PshLargeStrict-η : (α : PshHomStrict R (P ⇒PshLargeStrict Q)) →
      λPshHomStrict (×PshIntroStrict (π₁ R P ⋆PshHomStrict α) (π₂ R P) ⋆PshHomStrict appPshHomStrict)
        ≡ α
    ⇒PshLargeStrict-η α = makePshHomStrictPath
      (funExt₂ λ c r → makePshHomStrictPath
        (funExt₂ λ d (f , p) →
          sym (cong (λ x → α .N-ob c r .N-ob d (x , p)) (sym (C.⋆IdL f))
          ∙ funExt⁻ (funExt⁻ (cong N-ob (α .N-hom d c f r (f R.⋆ r) refl)) d) (C.id , p))))

module _ (C : Category ℓC ℓC') (ℓP : Level) where
  Exp-PRESHEAF :
    AllExponentiable (PRESHEAF C (ℓP ⊔ℓ ℓC ⊔ℓ ℓC'))
      (Cartesian-PRESHEAF C (ℓP ⊔ℓ ℓC ⊔ℓ ℓC') .CartesianCategory.bp)
  Exp-PRESHEAF P Q .UniversalElement.vertex = P ⇒PshLargeStrict Q
  Exp-PRESHEAF P Q .UniversalElement.element = appPshHomStrict P Q
  Exp-PRESHEAF P Q .UniversalElement.universal R =
    isoToIsEquiv (⇒PshLargeStrict-UMP P Q)

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  PshHetStrict : (F : Functor C D) (P : Presheaf C ℓP) (Q : Presheaf D ℓQ) → Type _
  PshHetStrict F P Q = PshHomStrict P (reindPsh F Q)

module _ {C : Category ℓC ℓC'} {Q : Presheaf C ℓQ} where
  Q→reindPshIdQ : PshHomStrict Q (reindPsh Id Q)
  -- Both of these solved for with auto
  Q→reindPshIdQ .N-ob = λ c z → z
  Q→reindPshIdQ .N-hom = λ c c' f p' p z → z

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
  where

  module _ (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ) where
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
  {Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ}
  {Qᴰ : Presheafᴰ P Cᴰ ℓQᴰ} where
  private
    module Cᴰ = Fibers Cᴰ
    module P = PresheafNotation P
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ

  congN-obⱽ : ∀ {Γ}{Γᴰ}{p p'}{pᴰ pᴰ'}
    → (αⱽ : PshHomStrict Pᴰ Qᴰ)
    → pᴰ Pᴰ.∫≡ pᴰ'
    → αⱽ .N-ob (Γ , Γᴰ , p) pᴰ Qᴰ.∫≡ αⱽ .N-ob (Γ , Γᴰ , p') pᴰ'
  congN-obⱽ {Γ} {Γᴰ} {p} {p'} {pᴰ} {pᴰ'} αⱽ pᴰ≡qᴰ i .fst = pᴰ≡qᴰ i .fst
  congN-obⱽ {Γ} {Γᴰ} {p} {p'} {pᴰ} {pᴰ'} αⱽ pᴰ≡qᴰ i .snd = αⱽ .N-ob (Γ , Γᴰ , pᴰ≡qᴰ i .fst) (pᴰ≡qᴰ i .snd)

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

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}{Q : Presheaf C ℓQ}
  (Pᴰ : Presheafᴰ (P ×Psh Q) Cᴰ ℓPᴰ)
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module P×Q = PresheafNotation (P ×Psh Q)
    module Pᴰ = PresheafᴰNotation Pᴰ

  ΣPsh : Presheafᴰ P Cᴰ (ℓ-max ℓQ ℓPᴰ)
  ΣPsh .F-ob (Γ , Γᴰ , p) .fst = Σ[ q ∈ Q.p[ Γ ] ] Pᴰ.p[ p , q ][ Γᴰ ]
  ΣPsh .F-ob (Γ , Γᴰ , p) .snd =
    isSetΣ (Q .F-ob Γ .snd) (λ x → Pᴰ .F-ob (Γ , Γᴰ , p , x) .snd)
  ΣPsh .F-hom =
    Hom/-elim (λ γ γᴰ γ⋆p≡γp (q , pᴰ) → (γ Q.⋆ q) ,
      Pᴰ .F-hom (γ , (γᴰ , PathEq× P.isSetPsh Q.isSetPsh γ⋆p≡γp (inr Eq.refl))) pᴰ)
  ΣPsh .F-id = funExt λ (q , pᴰ) → ΣPathP ((Q.⋆IdL q) ,
    (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆IdL _))
  ΣPsh .F-seq _ _ =
    funExt λ (q , pᴰ) → ΣPathP (Q.⋆Assoc _ _ _ , (Pᴰ.rectify $ Pᴰ.≡out $
      (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆Assoc _ _ _
      ∙ Pᴰ.⟨⟩⋆⟨ Pᴰ.⋆ᴰ-reind _ ⟩
      ∙ Pᴰ.⋆ᴰ-reind _))

  private
    module ΣPsh = PresheafᴰNotation ΣPsh

  ΣPsh-σ : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) ΣPsh)
  ΣPsh-σ .N-ob (_ , _ , (_ , q)) pᴰ = q , pᴰ
  ΣPsh-σ .N-hom _ _ =
    Hom/-elim λ γ γᴰ →
      elimPropEq P×Q.isSetPsh (λ _ → isPropΠ3 λ _ _ _ → ΣPsh.isSetPshᴰ _ _)
        λ {Eq.refl pᴰ pᴰ' e →
          (ΣPsh.rectifyOut $ sym $ ΣPsh.⋆ᴰ-reind _) ∙ ΣPathP (refl , e)}

  module _ {Rᴰ : Presheafᴰ P Cᴰ ℓRᴰ} where
    private
      module Rᴰ = PresheafᴰNotation Rᴰ
      ΣPsh-rec : PshHomStrict Pᴰ (reindPsh (Idᴰ /FⱽStrict π₁ _ _) Rᴰ) →
                 PshHomStrict ΣPsh Rᴰ
      ΣPsh-rec αᴰ .N-ob = λ c z →
        αᴰ .N-ob (c .fst , c .snd .fst , c .snd .snd , z .fst) (z .snd)
      ΣPsh-rec αᴰ .N-hom _ _ = Hom/-elim λ γ γᴰ →
        elimPropEq P.isSetPsh
          (λ _ → isPropΠ3 λ _ _ _ → Rᴰ.isSetPshᴰ _ _)
          (λ {Eq.refl p' p e →
            (Rᴰ.rectifyOut $ Rᴰ.⋆ᴰ-reind _)
            ∙ αᴰ .N-hom _ _
               (γ , γᴰ , PathEq× P.isSetPsh Q.isSetPsh (inr Eq.refl) (inl (cong fst e)))
               (p' .snd) (p .snd)
               (Pᴰ.rectifyOut ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in (cong snd e)))
           })

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  (P : Presheaf C ℓP)
  where
  private
    module P = PresheafNotation P
    module P×P = PresheafNotation (P ×Psh P)

  PathEqPsh' : Functor ((∫C (RedundElement (P ×Psh P))) ^op) (PROP ℓP)
  PathEqPsh' = mkFunctor (PROP ℓP) hasPropHomsPROP
    (λ (_ , p , p') → PathEq p p' , isPropPathEq P.isSetPsh)
    λ {(x , p , p')}{(y , q , q')} (f , fp,fp'≡q,q') →
      elimPropEq P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
        (λ {Eq.refl → elimPropBoth P×P.isSetPsh (λ _ → isPropPathEq P.isSetPsh)
          (λ e → inl (sym (cong fst e) ∙ cong snd e))
          (λ eq → inr (Eq.sym (Eq.ap fst eq) Eq.∙ Eq.ap snd eq))
          fp,fp'≡q,q'})

  PathEqPsh : Presheafᴰ (P ×Psh P) Cᴰ ℓP
  PathEqPsh = PROP→SET ∘F PathEqPsh' ∘F (∫F (Sndⱽ Cᴰ (RedundElement (P ×Psh P))) ^opF)

  private
    module PathEqPsh = PresheafᴰNotation PathEqPsh

  Refl : PshHomᴰStrict ΔPshHomStrict UnitPsh PathEqPsh
  Refl .N-ob = λ c z → inr Eq.refl
  Refl .N-hom c c' _ _ _ _ = isPropPathEq P.isSetPsh _ _

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  where

  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᴰ = PresheafᴰNotation Pᴰ

  PushPsh : Presheafᴰ Q Cᴰ (ℓP ⊔ℓ ℓPᴰ ⊔ℓ ℓQ)
  PushPsh =
    ΣPsh ((π₂ Q P *Strict Pᴰ) ×Psh
          (×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict α) *Strict PathEqPsh Q))

  private
    module PushPsh = PresheafᴰNotation PushPsh

  PushPsh-σ : PshHomᴰStrict α Pᴰ PushPsh
  PushPsh-σ .N-ob = λ c z → snd (c .snd) , z , inr Eq.refl
  PushPsh-σ .N-hom c c' =
    Hom/-elim (λ γ γᴰ → elimPropEq
      P.isSetPsh
      (λ _ → isPropΠ3 λ _ _ _ → PushPsh.isSetPshᴰ _ _)
      λ {Eq.refl pᴰ' pᴰ e → PushPsh.rectifyOut $
        (sym $ PushPsh.⋆ᴰ-reind _)
        ∙ ΣPathP (α .N-hom _ _ _ _ _ refl ,
            ΣPathP (refl , (ΣPathPProp (λ _ → isPropPathEq Q.isSetPsh)
            (Pᴰ.rectifyOut $ (sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.≡in e))))
        })

  module _ {Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ} where
    private
      module Qᴰ = PresheafᴰNotation Qᴰ
      module Cᴰ = Fibers Cᴰ

    push-recStrictⱽ : PshHomᴰStrict α Pᴰ Qᴰ → PshHomStrict PushPsh Qᴰ
    push-recStrictⱽ αᴰ .N-ob (Γ , Γᴰ , q) (p , pᴰ , q≡αp) =
      Qᴰ .F-hom (Category.id C , Categoryᴰ.idᴰ Cᴰ , inl (Q.⋆IdL _ ∙ sym (PathEq→Path Q.isSetPsh q≡αp)))
        (αᴰ .N-ob (Γ , Γᴰ , p) pᴰ)
    push-recStrictⱽ αᴰ .N-hom (Δ , Δᴰ , q) (Γ , Γᴰ , q') =
      Hom/-elim (λ γ γᴰ → elimPropPath Q.isSetPsh
        (λ _ → isPropΠ3 λ _ _ _ → Qᴰ.isSetPshᴰ _ _)
        λ γ⋆q'≡q (p , pᴰ , q'≡αp) (p' , pᴰ' , q≡αp') e →
          Qᴰ.rectifyOut $
          (sym $ Qᴰ.⋆ᴰ-reind _)
          ∙ Qᴰ.⟨⟩⋆⟨ sym $ Qᴰ.⋆ᴰ-reind _ ⟩
          ∙ sym (Qᴰ.⋆Assoc _ _ _)
          ∙ Qᴰ.⟨ Cᴰ.⋆IdR _ ⟩⋆⟨⟩
          ∙ ((sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _)
          ∙ (Qᴰ.≡in $ αᴰ .N-hom (Δ , Δᴰ , p') (Γ , Γᴰ , p)
                (γ , γᴰ , inl (cong fst e))
                pᴰ pᴰ'
                (Pᴰ.rectifyOut $ ((sym $ Pᴰ.⋆ᴰ-reind _) ∙ Pᴰ.⋆ᴰ-reind _)
                  ∙ Pᴰ.≡in (cong (λ z → z .snd .fst) e)))
          ∙ (sym $ Qᴰ.⋆IdL _)
          ∙ Qᴰ.⋆ᴰ-reind _)

module _ {C : Category ℓC ℓC'}
  {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP}
  {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module Qᴰ = PresheafᴰNotation Qᴰ
      module α*↓Pᴰ = PresheafᴰNotation (PushPsh α Pᴰ)

    push-UMP : Iso (PshHomStrict (PushPsh α Pᴰ) Qᴰ) (PshHomᴰStrict α Pᴰ Qᴰ)
    -- push-UMP : Iso (PshHomⱽ (push α Pᴰ) Qᴰ) (PshHomᴰ α Pᴰ Qᴰ)
    push-UMP .fun βⱽ = PushPsh-σ α Pᴰ ⋆PshHomStrict (α *StrictF βⱽ)
    push-UMP .inv = push-recStrictⱽ α Pᴰ
    push-UMP .sec βⱽ =
      makePshHomStrictPath
        (funExt₂ λ _ _ → Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆ᴰ-reind _ ∙ Qᴰ.⋆IdL _)
    push-UMP .ret βⱽ =
      makePshHomStrictPath
        (funExt₂ λ x → λ {(p , pᴰ , q≡αp) →
          -- {!!}
          elimPropPath Q.isSetPsh {M = λ pe →
           Qᴰ .F-hom
             (id C ,
              idᴰ Cᴰ ,
              inl
              (Q.⋆IdL
               (F-ob (∫F (Sndⱽ Cᴰ (RedundElement (Q ×Psh Q))) ^opF)
                (F-ob
                 ((Idᴰ /FⱽStrict ×PshIntroStrict (π₁ Q P) (π₂ Q P ⋆PshHomStrict α))
                  ^opF)
                 (x .fst , x .snd .fst , x .snd .snd , p))
                .snd .snd)
               ∙ (λ i → PathEq→Path Q.isSetPsh pe (~ i))))
             (βⱽ .N-ob
              (F-ob ((Idᴰ /FⱽStrict α) ^opF) (x .fst , x .snd .fst , p))
              (p , pᴰ , inr Eq.refl))
             ≡ βⱽ .N-ob x (p , pᴰ , pe)}

            (λ _ → Qᴰ.isSetPshᴰ _ _) (λ {q≡αp →
              Qᴰ.rectifyOut $ (sym $ Qᴰ.⋆ᴰ-reind _) ∙ Qᴰ.⋆IdL _
              ∙ ΣPathP (sym q≡αp , (Qᴰ.rectifyOut $ congN-obⱽ βⱽ
                  (α*↓Pᴰ.≡in {pth = sym q≡αp} (
                     ΣPathP (refl ,
                             ΣPathP (refl ,
                                     isProp→PathP (λ _ _ → isPropPathEq Q.isSetPsh _) _ _))))))
            })
            q≡αp
          }
        )

module _ {C : Category ℓC ℓC'} {Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ}
  (α : PshHomStrict P Q)
  (Pᴰ : Presheafᴰ P Cᴰ ℓPᴰ)
  (Qᴰ : Presheafᴰ Q Cᴰ ℓQᴰ)
  where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Pᴰ = PresheafᴰNotation Pᴰ
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Cᴰ = Fibers Cᴰ

  -- Frobenius Reciprocity: ∃α (Pᴰ × α*Qᴰ) ≅ (∃α Pᴰ) × Qᴰ
  FrobeniusReciprocityStrict-ptwise : ∀ ((Γ , Γᴰ , q) : (Cᴰ / Q) .Category.ob) →
    Iso (Σ[ p ∈ P.p[ Γ ] ] (Pᴰ.p[ p ][ Γᴰ ] × Qᴰ.p[ α .N-ob Γ p ][ Γᴰ ]) × PathEq q (α .N-ob Γ p))
        ((Σ[ p ∈ P.p[ Γ ] ] Pᴰ.p[ p ][ Γᴰ ] × PathEq q (α .N-ob Γ p)) × Qᴰ.p[ q ][ Γᴰ ])
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.fun (p , (pᴰ , qᴰ) , q≡αp) =
    (p , pᴰ , q≡αp) , Qᴰ.reind (sym $ PathEq→Path Q.isSetPsh q≡αp) qᴰ
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.inv ((p , pᴰ , q≡αp) , qᴰ) =
    p , (pᴰ , Qᴰ.reind (PathEq→Path Q.isSetPsh q≡αp) qᴰ) , q≡αp
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.sec ((p , pᴰ , q≡αp) , qᴰ) =
    ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _))
  FrobeniusReciprocityStrict-ptwise (Γ , Γᴰ , q) .Iso.ret (p , (pᴰ , qᴰ) , q≡αp) =
    ΣPathP (refl , ΣPathP (ΣPathP (refl , (Qᴰ.rectifyOut $ Qᴰ.reind-filler⁻ _ ∙ Qᴰ.reind-filler⁻ _)) , refl))

  private
    -- ∃α (Pᴰ × α*Qᴰ)
    LHS : Presheafᴰ Q Cᴰ _
    LHS = PushPsh α (Pᴰ ×Psh (α *Strict Qᴰ))

    -- (∃α Pᴰ) × Qᴰ
    RHS : Presheafᴰ Q Cᴰ _
    RHS = (PushPsh α Pᴰ) ×Psh Qᴰ

    module LHSMod = PresheafᴰNotation LHS
    module RHSMod = PresheafᴰNotation RHS

  -- Naturality condition: for f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ] and p at (Γ,Γᴰ,q'),
  -- fun (iso at Δ,Δᴰ,q) (f ⋆ p) ≡ f ⋆ (fun (iso at Γ,Γᴰ,q') p)
  FrobeniusReciprocityStrict-natural :
    ∀ (Δ,Δᴰ,q : (Cᴰ / Q) .Category.ob) (Γ,Γᴰ,q' : (Cᴰ / Q) .Category.ob)
    (f : (Cᴰ / Q) [ Δ,Δᴰ,q , Γ,Γᴰ,q' ])
    (p : ⟨ LHS .F-ob Γ,Γᴰ,q' ⟩) →
    fun (FrobeniusReciprocityStrict-ptwise Δ,Δᴰ,q) (LHS .F-hom f p)
      ≡
    RHS .F-hom f (fun (FrobeniusReciprocityStrict-ptwise Γ,Γᴰ,q') p)
  FrobeniusReciprocityStrict-natural (Δ , Δᴰ , q) (Γ , Γᴰ , q') (γ , γᴰ , γ⋆q'≡q) (p , (pᴰ , qᴰ) , q'≡αp) =
    ΣPathP (refl , (Qᴰ.rectifyOut $
      Qᴰ.reind-filler⁻ _
      ∙ (sym $ Qᴰ.⋆ᴰ-reind _)
      ∙ Qᴰ.⟨⟩⋆⟨ Qᴰ.reind-filler _ ⟩ ∙ Qᴰ.⋆ᴰ-reind _))

  FrobeniusReciprocityStrict : PshIsoStrict LHS RHS
  FrobeniusReciprocityStrict = Isos→PshIsoStrict
    FrobeniusReciprocityStrict-ptwise
    FrobeniusReciprocityStrict-natural

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

  private
    F : Functor (Cᴰ / P) (Cᴰ / Q)
    F = Idᴰ /FⱽStrict α

  *Strict⇒ⱽ→⇒ⱽ*Strict :
    PshHomStrict
      (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
      ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
  *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-ob c' (γ , qᴰ) =
    f .N-ob (F ⟅ c' ⟆) (F ⟪ γ ⟫ , qᴰ)
  *Strict⇒ⱽ→⇒ⱽ*Strict .N-ob c f .N-hom c'' c' e (γ' , qᴰ') (γ , qᴰ) eq =
    f .N-hom (F ⟅ c'' ⟆) (F ⟅ c' ⟆) (F ⟪ e ⟫) (F ⟪ γ' ⟫ , qᴰ') (F ⟪ γ ⟫ , qᴰ)
      (ΣPathP (sym (F .F-seq e γ') ∙ cong (F .F-hom) (cong fst eq) , cong snd eq))
  *Strict⇒ⱽ→⇒ⱽ*Strict .N-hom c c' h f' f eq =
    makePshHomStrictPath (funExt₂ λ d (γ , qᴰ) →
      cong (λ δ → f' .N-ob (F ⟅ d ⟆) (δ , qᴰ)) (F .F-seq γ h)
      ∙ funExt⁻ (funExt⁻ (cong N-ob eq) (F ⟅ d ⟆)) (F ⟪ γ ⟫ , qᴰ))

  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
    module Qᴰ = PresheafᴰNotation Qᴰ
    module Rᴰ = PresheafᴰNotation Rᴰ

  ⇒ⱽ*Strict→*Strict⇒ⱽ :
    PshHomStrict
      ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ))
      (α *Strict (Qᴰ ⇒PshLargeStrict Rᴰ))
  ⇒ⱽ*Strict→*Strict⇒ⱽ =
    push-UMP α ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) (Qᴰ ⇒PshLargeStrict Rᴰ) .Iso.fun
      (λPshHomStrict Qᴰ Rᴰ
        (invPshIsoStrict
          (FrobeniusReciprocityStrict α
           ((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) Qᴰ)
             .PshIsoStrict.trans
          ⋆PshHomStrict push-UMP α (((α *Strict Qᴰ) ⇒PshLargeStrict (α *Strict Rᴰ)) ×Psh
                                     (α *Strict Qᴰ)) Rᴰ .inv
                        (appPshHomStrict (α *Strict Qᴰ) (α *Strict Rᴰ))))

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
  (ℓP : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
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

module _
  (C : Category ℓC ℓC')
  (ℓP : Level)
  (Cᴰ : Categoryᴰ C ℓCᴰ ℓCᴰ')
  (ℓPᴰ : Level)
  where
  private
     the-ℓ = ℓC ⊔ℓ ℓC' ⊔ℓ ℓP
     the-ℓᴰ = the-ℓ ⊔ℓ ℓCᴰ ⊔ℓ ℓCᴰ' ⊔ℓ ℓPᴰ
     PSHᴰ = PRESHEAFᴰ C the-ℓ Cᴰ the-ℓᴰ
     module PSHᴰ = Fibers PSHᴰ
  module _ {P : Presheaf C the-ℓ} (Pᴰ : Presheafᴰ P Cᴰ the-ℓᴰ) where
    private
      module Pᴰ = PresheafᴰNotation Pᴰ

    PSHᴰLRⱽ : LRⱽ PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) Pᴰ
    PSHᴰLRⱽ {Γ = Q} Qᴰ α = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) lrⱽue
      where
        module Qᴰ = PresheafᴰNotation Qᴰ

        lrⱽue : UEⱽ
                 ((PSHᴰ [-][-, Qᴰ ]) ×ⱽPsh
                  reindᴰRedundPshHom
                  (yoRecHom PSHᴰ (λ {w} {x} {y} {z} f g h → Eq.refl) α)
                  (PSHᴰ [-][-, Pᴰ ]))
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

    PSHᴰExpsⱽ : Exponentialsⱽ PSHᴰ
      (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl) Pᴰ PSHᴰLRⱽ
    PSHᴰExpsⱽ Qᴰ = UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) (expUE Qᴰ)
      where
      expUE : ExponentialsⱽUE PSHᴰ
        (λ {w} {x} {y} {z} f g h → Eq.refl) (λ {x} {y} f → Eq.refl)
        Pᴰ PSHᴰLRⱽ (λ {x} {y} f → Eq.refl)
      expUE Qᴰ .UEⱽ.v = Pᴰ ⇒PshLargeStrict Qᴰ
      -- Pᴰ⇒Qᴰ × Id*Pᴰ → Id*Qᴰ
      expUE Qᴰ .UEⱽ.e =
        ×PshIntroStrict (π₁ _ _) (π₂ _ _ ⋆PshHomStrict *StrictIdIntro⁻ Pᴰ)
        ⋆PshHomStrict appPshHomStrict Pᴰ Qᴰ
        ⋆PshHomStrict *StrictIdIntro Qᴰ
      expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .fst αᴰ =
        λPshHomStrict (α *Strict Pᴰ) (α *Strict Qᴰ) αᴰ
        ⋆PshHomStrict ⇒ⱽ*Strict→*Strict⇒ⱽ α Pᴰ Qᴰ
      expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .fst αᴰ =
        makePshHomStrictPath (funExt₂ λ u v →
          Qᴰ.rectifyOut $ {!!} ∙ {!!})
        where module Qᴰ = PresheafᴰNotation Qᴰ
      expUE Qᴰ .UEⱽ.universal .isPshIso'.nIso (R , Rᴰ , α) .snd .snd αᴰ =
        makePshHomStrictPath {!!}
        where module Qᴰ = PresheafᴰNotation Qᴰ
