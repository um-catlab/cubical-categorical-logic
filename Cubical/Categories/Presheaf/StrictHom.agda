{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.StrictHom where

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
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More
private
  variable
    ℓ ℓ' ℓs ℓr ℓc ℓc' ℓp ℓq ℓP ℓQ ℓR ℓS ℓS' ℓS'' : Level
    ℓC ℓC' ℓD ℓD' ℓCᴰ ℓCᴰ' ℓDᴰ ℓDᴰ' ℓPᴰ ℓQᴰ ℓRᴰ : Level

open Functor
open Iso
open NatIso
open NatTrans

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

  module _ {P : Presheaf C ℓp} {Q : Presheaf C ℓq} {R : Presheaf C ℓr} {S : Presheaf C ℓs}
    (α : PshHomStrict R P) (β : PshHomStrict S Q)
    where
    _×PshHomStrict_ : PshHomStrict (R ×Psh S) (P ×Psh Q)
    _×PshHomStrict_ = ×PshIntroStrict (π₁ _ _ ⋆PshHomStrict α) (π₂ _ _ ⋆PshHomStrict β)

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

  PSH1 : Terminal' PRESHEAF
  PSH1 .UniversalElement.vertex = Unit*Psh
  PSH1 .UniversalElement.element = tt
  PSH1 .UniversalElement.universal _ =
    isoToIsEquiv
      (iso (λ _ → tt) (λ _ → Unit*Psh-introStrict)
         (λ _ → refl) (λ _ → refl))

  PSHBP : BinProducts PRESHEAF
  PSHBP (P , Q) .UniversalElement.vertex = P ×Psh Q
  PSHBP (P , Q) .UniversalElement.element = π₁ P Q , π₂ P Q
  PSHBP (P , Q) .UniversalElement.universal R = isoToIsEquiv (×PshStrict-UMP P Q)

  Cartesian-PRESHEAF : CartesianCategory _ _
  Cartesian-PRESHEAF .CartesianCategory.C = PRESHEAF
  Cartesian-PRESHEAF .CartesianCategory.term = PSH1
  Cartesian-PRESHEAF .CartesianCategory.bp = PSHBP

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

  isFaithfulYOStrict : isFaithful YOStrict
  isFaithfulYOStrict x y f g p =
    (sym $ C.⋆IdL f) ∙ (λ i → p i .N-ob x C.id)  ∙ C.⋆IdL g

  -- If YOStrict factors as G ∘F F, then F is faithful
  module _ {D : Category ℓD ℓD'}
    {F : Functor C D}{G : Functor D (PRESHEAF C ℓ')}
    (YO≡GF : YOStrict ≡ G ∘F F) where
    isFaithful-YOStrict-factor : isFaithful F
    isFaithful-YOStrict-factor x y f g p =
      subst isFaithful YO≡GF isFaithfulYOStrict x y f g
        (congS (G .F-hom) p)

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

module _ {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} where
  reindPshFStrict : (F : Functor C D) → Functor (PRESHEAF D ℓQ) (PRESHEAF C ℓQ)
  reindPshFStrict F .F-ob = reindPsh F
  reindPshFStrict F .F-hom α .N-ob = λ c → α .N-ob (F ⟅ c ⟆)
  reindPshFStrict F .F-hom α .N-hom = λ c c' f → α .N-hom _ _ (F ⟪ f ⟫)
  reindPshFStrict F .F-id = refl
  reindPshFStrict F .F-seq _ _ = refl

module _ (C : Category ℓC ℓC') (ℓP : Level) where
  CCC-PRESHEAF : CartesianClosedCategory _ _
  CCC-PRESHEAF .CartesianClosedCategory.CC = Cartesian-PRESHEAF C (ℓP ⊔ℓ ℓC' ⊔ℓ ℓC)
  CCC-PRESHEAF .CartesianClosedCategory.exps P Q = Exp-PRESHEAF C ℓP P Q
