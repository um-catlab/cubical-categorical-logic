module Cubical.Categories.Presheaf.StrictHom.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
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
open import Cubical.Categories.Instances.Lift
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.TotalCategory.Base
open import Cubical.Categories.Instances.Elements
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
  (isPshIso' ; PshIso' ; PshHom ; _⋆NatTransPshHom_ ; _⋆PshHom_ ; PshIso ; makePshHomPath)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Tensor
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.BinProduct hiding (π₁ ; π₂)
open import Cubical.Categories.Profunctor.Relator
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

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  where

  module _ (α : PshHom P Q) where
    PshHom→PshHomStrict : PshHomStrict P Q
    PshHom→PshHomStrict .N-ob = α .PshHom.N-ob
    PshHom→PshHomStrict .N-hom c c' f p p' e =
      sym (α .PshHom.N-hom _ _ f p) ∙ cong (α .PshHom.N-ob c) e

  module _ (α : PshIso P Q) where
    PshIso→PshIsoStrict : PshIsoStrict P Q
    PshIso→PshIsoStrict .PshIsoStrict.trans = PshHom→PshHomStrict (α .PshIso.trans)
    PshIso→PshIsoStrict .PshIsoStrict.nIso = α .PshIso.nIso

  module _ (α : PshHomStrict P Q) where
    PshHomStrict→PshHom : PshHom P Q
    PshHomStrict→PshHom .PshHom.N-ob = α .N-ob
    PshHomStrict→PshHom .PshHom.N-hom c c' f p = sym $ α .N-hom c c' f p (P .F-hom f p) refl

  module _ (α : PshIsoStrict P Q) where
    PshIsoStrict→PshIso : PshIso P Q
    PshIsoStrict→PshIso .PshIso.trans = PshHomStrict→PshHom (PshIsoStrict.trans α)
    PshIsoStrict→PshIso .PshIso.nIso = PshIsoStrict.nIso α

  PshHom≅PshHomStrict : Iso (PshHom P Q) (PshHomStrict P Q)
  PshHom≅PshHomStrict .fun = PshHom→PshHomStrict
  PshHom≅PshHomStrict .inv = PshHomStrict→PshHom
  PshHom≅PshHomStrict .sec β = makePshHomStrictPath refl
  PshHom≅PshHomStrict .ret α = makePshHomPath refl

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

module _ {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} where
  open PshIsoStrict

  _⋆PshIsoStrict_ : PshIsoStrict P Q → PshIsoStrict Q R → PshIsoStrict P R
  (α ⋆PshIsoStrict β) .trans = α .trans ⋆PshHomStrict β .trans
  (α ⋆PshIsoStrict β) .nIso x =
    IsoToIsIso $
      compIso (isIsoToIso (α .nIso x)) (isIsoToIso (β .nIso x))
  infixr 9 _⋆PshIsoStrict_

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where
  open PshIsoStrict
  idPshIsoStrict : PshIsoStrict P P
  idPshIsoStrict .trans = idPshHomStrict
  idPshIsoStrict .nIso _ = IsoToIsIso idIso

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  (α : PshHomStrict P Q)
  where
  ⋆PshHomStrictIdL : idPshHomStrict {P = P} ⋆PshHomStrict α ≡ α
  ⋆PshHomStrictIdL = refl
  ⋆PshHomStrictIdR : α ⋆PshHomStrict idPshHomStrict {P = Q}  ≡ α
  ⋆PshHomStrictIdR = refl

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

  private
    open isIsoC renaming (inv to invC)

    toNT : ∀ {P Q : Presheaf C ℓP} → PshHomStrict P Q → NatTrans P Q
    toNT α .NatTrans.N-ob = α .N-ob
    toNT α .NatTrans.N-hom f = funExt λ a → sym (α .N-hom _ _ f a _ refl)

    fromNT : ∀ {P Q : Presheaf C ℓP} → NatTrans P Q → PshHomStrict P Q
    fromNT α .N-ob = α .NatTrans.N-ob
    fromNT α .N-hom c c' f p' p e =
      sym (funExt⁻ (α .NatTrans.N-hom f) p') ∙ cong (α .NatTrans.N-ob _) e

    PRESHEAFIso→NatIso : ∀ {P Q : Presheaf C ℓP} →
      CatIso PRESHEAF P Q → NatIso P Q
    PRESHEAFIso→NatIso ci .trans = toNT (ci .fst)
    PRESHEAFIso→NatIso ci .nIso x .invC = ci .snd .invC .N-ob x
    PRESHEAFIso→NatIso ci .nIso x .sec = funExt⁻ (cong N-ob (ci .snd .sec)) x
    PRESHEAFIso→NatIso ci .nIso x .ret = funExt⁻ (cong N-ob (ci .snd .ret)) x

    NatIso→PRESHEAFIso : ∀ {P Q : Presheaf C ℓP} →
      NatIso P Q → CatIso PRESHEAF P Q
    NatIso→PRESHEAFIso ni = theFwd , isIsoFwd
      where
        theFwd : PshHomStrict _ _
        theFwd = fromNT (ni .trans)

        theIso : isPshIsoStrict theFwd
        theIso x = ni .nIso x .invC ,
          (λ b → funExt⁻ (ni .nIso x .sec) b) ,
          (λ a → funExt⁻ (ni .nIso x .ret) a)

        theInv : PshHomStrict _ _
        theInv = invPshIsoStrict (pshiso theFwd theIso) .PshIsoStrict.trans

        isIsoFwd : isIsoC PRESHEAF theFwd
        isIsoFwd .invC = theInv
        isIsoFwd .sec =
          makePshHomStrictPath (funExt₂ λ c q → theIso c .snd .fst q)
        isIsoFwd .ret =
          makePshHomStrictPath (funExt₂ λ c p → theIso c .snd .snd p)

    Iso-PRESHEAFIso-NatIso : ∀ {P Q : Presheaf C ℓP} →
      Iso (CatIso PRESHEAF P Q) (NatIso P Q)
    Iso-PRESHEAFIso-NatIso .fun = PRESHEAFIso→NatIso
    Iso-PRESHEAFIso-NatIso .inv = NatIso→PRESHEAFIso
    Iso-PRESHEAFIso-NatIso .sec ni = NatIso≡ refl
    Iso-PRESHEAFIso-NatIso .ret ci = CatIso≡ _ ci (makePshHomStrictPath refl)

    PRESHEAFIso≃NatIso : ∀ {P Q : Presheaf C ℓP} →
      CatIso PRESHEAF P Q ≃ NatIso P Q
    PRESHEAFIso≃NatIso = isoToEquiv Iso-PRESHEAFIso-NatIso

    Path→PRESHEAFIso→NatIso : ∀ {P Q : Presheaf C ℓP} → (p : P ≡ Q) →
      pathToNatIso p ≡ PRESHEAFIso→NatIso (pathToIso p)
    Path→PRESHEAFIso→NatIso {P = P} =
      J (λ _ p → pathToNatIso p ≡ PRESHEAFIso→NatIso (pathToIso p))
        (NatIso≡ refl-helper)
      where
        refl-helper : _
        refl-helper i x =
          ((λ i → pathToIso-refl {C = SET ℓP} {x = P .F-ob x} i .fst)
          ∙ (λ i → pathToIso-refl {C = PRESHEAF} {x = P} (~ i) .fst .N-ob x)) i

  isUnivalentPRESHEAF : isUnivalent PRESHEAF
  isUnivalentPRESHEAF .isUnivalent.univ P Q =
    isEquiv[equivFunA≃B∘f]→isEquiv[f] _ PRESHEAFIso≃NatIso
      (subst isEquiv (λ i p → Path→PRESHEAFIso→NatIso p i)
        (Path≃NatIso isUnivalentSET .snd))

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

  reindPshHomStrict : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshHomStrict P Q)
    → PshHomStrict (reindPsh F P) (reindPsh F Q)
  reindPshHomStrict F α .N-ob c = α .N-ob _
  reindPshHomStrict F α .N-hom c c' f = α .N-hom _ _ _

  open PshIsoStrict
  reindPshIsoStrict : {P : Presheaf D ℓP}{Q : Presheaf D ℓQ}
    → (F : Functor C D) (α : PshIsoStrict P Q)
    → PshIsoStrict (reindPsh F P) (reindPsh F Q)
  reindPshIsoStrict F α .trans = reindPshHomStrict F (α .trans)
  reindPshIsoStrict F α .nIso x .fst = α .nIso _ .fst
  reindPshIsoStrict F α .nIso x .snd .fst = α .nIso _ .snd .fst
  reindPshIsoStrict F α .nIso x .snd .snd = α .nIso _ .snd .snd

module _ {C : Category ℓC ℓC'} (P : Presheaf C ℓP) where
  private
    module C = Category C
    module P = PresheafNotation P
  -- Universe-polymorphic Yoneda recursion principle
  yoRecStrict : ∀ {c} → P.p[ c ] → PshHomStrict (C [-, c ]) P
  yoRecStrict p .PshHomStrict.N-ob _ = P._⋆ p
  yoRecStrict p .PshHomStrict.N-hom _ _ _ _ _ f⋆p'≡p = sym (P.⋆Assoc _ _ _) ∙ P.⟨ f⋆p'≡p ⟩⋆⟨⟩

-- Helper: precomposing with a PshIsoStrict gives an Iso on hom sets
module _ {C : Category ℓC ℓC'}
  {P : Presheaf C ℓP} {Q : Presheaf C ℓQ} {R : Presheaf C ℓR}
  (isoᴾᴼ : PshIsoStrict P Q)
  where
  private
    f = isoᴾᴼ .PshIsoStrict.trans
    g = invPshIsoStrict isoᴾᴼ .PshIsoStrict.trans
    sec' : ∀ c q → f .N-ob c (g .N-ob c q) ≡ q
    sec' c = isoᴾᴼ .PshIsoStrict.nIso c .snd .fst
    ret' : ∀ c p → g .N-ob c (f .N-ob c p) ≡ p
    ret' c = isoᴾᴼ .PshIsoStrict.nIso c .snd .snd

  precompPshIsoStrict : Iso (PshHomStrict Q R) (PshHomStrict P R)
  precompPshIsoStrict .fun β = f ⋆PshHomStrict β
  precompPshIsoStrict .inv γ = g ⋆PshHomStrict γ
  precompPshIsoStrict .sec γ = makePshHomStrictPath
    (funExt₂ λ c p → cong (γ .N-ob c) (ret' c p))
  precompPshIsoStrict .ret β = makePshHomStrictPath
    (funExt₂ λ c q → cong (β .N-ob c) (sec' c q))

module _ {C : Category ℓc ℓc'} where
  step-PshIsoStrict : ∀ (P : Presheaf C ℓp) {Q : Presheaf C ℓq} {R : Presheaf C ℓr}
    → PshIsoStrict Q R → PshIsoStrict P Q → PshIsoStrict P R
  step-PshIsoStrict _ g f = f ⋆PshIsoStrict g

  infixr  2 step-PshIsoStrict
  syntax step-PshIsoStrict P Q f = P PshIsoStrict⟨ f ⟩ Q

  _∎PshIsoStrict : ∀ (P : Presheaf C ℓp) → PshIsoStrict P P
  P ∎PshIsoStrict = idPshIsoStrict {P = P}

  infix   3 _∎PshIsoStrict
