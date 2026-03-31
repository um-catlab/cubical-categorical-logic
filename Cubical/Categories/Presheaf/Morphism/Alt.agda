{- This is intended to replace Presheaf.Morphism upstream -}
module Cubical.Categories.Presheaf.Morphism.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv.More

open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq
import Cubical.Data.Equality.More as Eq
open import Cubical.HITs.PathEq
open import Cubical.HITs.Join

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Instances.Elements
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Yoneda

{-

  Given two presheaves P and Q on the same category C, a morphism
  between them is a natural transformation. Here we generalize this to
  situations where P and Q are presheaves on *different*
  categories. This is equivalent to the notion of morphism of
  fibrations if viewing P and Q as discrete fibrations.

  Given a functor F : C → D, a presheaf P on C and a presheaf Q on D,
  we can define a homomorphism from P to Q over F as a natural
  transformation from P to Q o F^op. (if we had implicit cumulativity)

  These are the homs of a 2-category of presheaves displayed over the
  2-category of categories.

-}
private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr ℓs : Level

open Category
open Contravariant
open UniversalElement

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q

  PshHomΣ : Type _
  PshHomΣ = Σ[ α ∈ (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) ]
    (∀ x y (f : C [ x , y ]) (p : P.p[ y ]) →
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))

  isPropN-hom : ∀ (α : (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ])) →
    isProp (∀ x y (f : C [ x , y ]) (p : P.p[ y ])→
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))
  isPropN-hom =
    λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Q.isSetPsh _ _

  isSetPshHomΣ : isSet PshHomΣ
  isSetPshHomΣ =
    isSetΣ (isSetΠ (λ _ → isSet→ Q.isSetPsh)) λ _ → isProp→isSet (isPropN-hom _)

  PshHom-N-hom-ty : ((c : C.ob) → P.p[ c ] → Q.p[ c ]) → Type _
  PshHom-N-hom-ty N-ob = ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
    N-ob c (f P.⋆ p) ≡ (f Q.⋆ N-ob c' p)

  -- Natural transformation between presheaves of different levels
  record PshHom : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
    no-eta-equality
    constructor pshhom
    field
      N-ob : ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]
      N-hom : ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
        N-ob c (f P.⋆ p) ≡ (f Q.⋆ N-ob c' p)

  record PshHom' : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
    no-eta-equality
    constructor pshhom
    field
      N-ob : ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]
      N-hom : ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
        PathEq (N-ob c (f P.⋆ p)) (f Q.⋆ N-ob c' p)

  record PshHomEq : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
    constructor pshhom
    field
      N-ob : ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]
      N-hom : ∀ c c' (f : C [ c , c' ]) (p' : P.p[ c' ]) (p : P.p[ c ]) →
        f P.⋆ p' Eq.≡ p                      -- Element P [ f ][ p' , p ]
        → (f Q.⋆ N-ob c' p') Eq.≡ (N-ob c p) -- Element Q [ f ][ α p' , α p ]

  PshHomΣIso : Iso PshHom PshHomΣ
  unquoteDef PshHomΣIso = defineRecordIsoΣ PshHomΣIso (quote (PshHom))

  isSetPshHom : isSet PshHom
  isSetPshHom = isOfHLevelRetractFromIso 2 PshHomΣIso isSetPshHomΣ

  isPropN-HomEq : ∀ (α : (x : ob C) → P.p[ x ] → Q.p[ x ]) → isProp (∀ c c' (f : C [ c , c' ]) (p' : P.p[ c' ]) (p : P.p[ c ]) →
        f P.⋆ p' Eq.≡ p
        → (f Q.⋆ α c' p') Eq.≡ (α c p))
  isPropN-HomEq α = isPropΠ (λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isProp→ (Eq.isSet→isSetEq Q.isSetPsh))

  PshHomEqΣ = Σ[ α ∈ (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) ]
    ∀ c c' (f : C [ c , c' ]) (p' : P.p[ c' ]) (p : P.p[ c ]) →
        f P.⋆ p' Eq.≡ p
        → (f Q.⋆ α c' p') Eq.≡ (α c p)

  PshHomEqΣIso : Iso PshHomEq PshHomEqΣ
  unquoteDef PshHomEqΣIso = defineRecordIsoΣ PshHomEqΣIso (quote (PshHomEq))



  isSetPshHomEq : isSet PshHomEq
  isSetPshHomEq = isOfHLevelRetractFromIso 2 PshHomEqΣIso
    (isSetΣ (isSetΠ λ _ → isSetΠ λ _ → Q.isSetPsh) λ α →
      isProp→isSet (isPropN-HomEq α))

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓp}
  where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  NatTrans→PshHom : NatTrans P Q → PshHom P Q
  NatTrans→PshHom α .PshHom.N-ob = α .NatTrans.N-ob
  NatTrans→PshHom α .PshHom.N-hom x y f = funExt⁻ (α .NatTrans.N-hom f)

  PshHom→NatTrans : PshHom P Q → NatTrans P Q
  PshHom→NatTrans α .NatTrans.N-ob = α .PshHom.N-ob
  PshHom→NatTrans α .NatTrans.N-hom f = funExt (α .PshHom.N-hom _ _ f)

open PshHom
module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  makePshHomΣPath : ∀ {α β : PshHomΣ P Q} → α .fst ≡ β .fst
   → α ≡ β
  makePshHomΣPath = ΣPathPProp (isPropN-hom P Q)

  makePshHomPath : ∀ {α β : PshHom P Q} → α .N-ob ≡ β .N-ob
   → α ≡ β
  makePshHomPath {α} {β} N-ob≡ =
    isoFunInjective (PshHomΣIso P Q) α β (makePshHomΣPath N-ob≡)

  makePshHomEqPath : ∀ {α β : PshHomEq P Q} → α .PshHomEq.N-ob ≡ β .PshHomEq.N-ob
   → α ≡ β
  makePshHomEqPath ob≡ = isoFunInjective (PshHomEqΣIso P Q) _ _ (ΣPathPProp (isPropN-HomEq P Q) ob≡)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where
  idPshHom : PshHom P P
  idPshHom .N-ob x z = z
  idPshHom .N-hom x y f p = refl

  idPshHom' : PshHom' P P
  idPshHom' .PshHom'.N-ob = λ c z → z
  idPshHom' .PshHom'.N-hom = λ c c' f p → inr Eq.refl

  idPshHomEq : PshHomEq P P
  idPshHomEq .PshHomEq.N-ob = λ c z → z
  idPshHomEq .PshHomEq.N-hom = λ c c' f p' p z → z

module _ {C : Category ℓc ℓc'} where
  _⋆PshHom_ : ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} →
    PshHom P Q → PshHom Q R → PshHom P R
  (α ⋆PshHom β) .N-ob x p = β .N-ob x (α .N-ob x p)
  (α ⋆PshHom β) .N-hom x y f p =
    cong (β .N-ob _) (α .N-hom x y f p)
    ∙ β .N-hom x y f (α .N-ob y p)
  infixr 9 _⋆PshHom_

  _⋆PshHomEq_ : ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} →
    PshHomEq P Q → PshHomEq Q R → PshHomEq P R
  (α ⋆PshHomEq β) .PshHomEq.N-ob = λ c z → β .PshHomEq.N-ob c (α .PshHomEq.N-ob c z)
  (α ⋆PshHomEq β) .PshHomEq.N-hom = λ c c' f p' p z →
                                       β .PshHomEq.N-hom c c' f (α .PshHomEq.N-ob c' p')
                                       (α .PshHomEq.N-ob c p) (α .PshHomEq.N-hom c c' f p' p z)
  infixr 9 _⋆PshHomEq_


  module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
      module R = PresheafNotation R
    _⋆PshHom'_ : PshHom' P Q → PshHom' Q R → PshHom' P R
    (α ⋆PshHom' β) .PshHom'.N-ob c p = β .PshHom'.N-ob c (α .PshHom'.N-ob c p)
    (α ⋆PshHom' β) .PshHom'.N-hom c c' f p =
      epSubst Q.isSetPsh goal1 (symPE Q.isSetPsh $ α .PshHom'.N-hom c c' f p) $
      epSubst R.isSetPsh goal2 (symPE R.isSetPsh $ β .PshHom'.N-hom c c' f _) (inr Eq.refl)
      where
      goal1 : ∀ (αfp : Q.p[ c ]) → Type _
      goal1 αfp = PathEq
        (β .PshHom'.N-ob c αfp)
        (f R.⋆ (β .PshHom'.N-ob c' (α .PshHom'.N-ob c' p)))
      goal2 : ∀ (βfα : R.p[ c ] ) → Type _
      goal2 βfα = PathEq
        βfα
        ((f R.⋆ (β .PshHom'.N-ob c' (α .PshHom'.N-ob c' p))))

  _⋆PshHomNatTrans_ :
    ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓq} →
      PshHom P Q → NatTrans Q R → PshHom P R
  α ⋆PshHomNatTrans β = α ⋆PshHom NatTrans→PshHom β
  _⋆NatTransPshHom_ :
    ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓp}{R : Presheaf C ℓr} →
      NatTrans P Q → PshHom Q R → PshHom P R
  α ⋆NatTransPshHom β = NatTrans→PshHom α ⋆PshHom β

  module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{α : PshHom P Q} where
    id⋆α≡α : idPshHom {C = C} ⋆PshHom α ≡ α
    id⋆α≡α = makePshHomPath refl

open Functor
module _ {C : Category ℓc ℓc'} where
  PshHomPsh :
    ∀ (Q : Presheaf C ℓq) →
      Presheaf (PresheafCategory C ℓp) (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓq) ℓp)
  PshHomPsh Q .F-ob P = (PshHom P Q) , (isSetPshHom _ _)
  PshHomPsh Q .F-hom α β = α ⋆NatTransPshHom β
  PshHomPsh Q .F-id = funExt (λ _ → makePshHomPath refl)
  PshHomPsh Q .F-seq α α' = funExt λ _ → makePshHomPath refl

  PshHomProf :
    Profunctor
      (PresheafCategory C ℓq)
      (PresheafCategory C ℓp)
      (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHomProf .F-ob Q = PshHomPsh Q
  PshHomProf .F-hom β .NatTrans.N-ob P α = α ⋆PshHomNatTrans β
  PshHomProf .F-hom β .NatTrans.N-hom α = funExt λ _ → makePshHomPath refl
  PshHomProf .F-id =
    makeNatTransPath (funExt (λ _ → funExt λ _ → makePshHomPath refl))
  PshHomProf .F-seq β β' =
    makeNatTransPath (funExt λ _ → funExt λ _ → makePshHomPath refl)

  PshHomBif : Bifunctor ((PresheafCategory C ℓp) ^op) (PresheafCategory C ℓq)
    (SET (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq))
  PshHomBif = Sym $ CurriedToBifunctor PshHomProf

{- a PshIso is a PshHom whose underlying functions are iso -}
module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  isPshIso : PshHom P Q → Type _
  isPshIso α = ∀ x → isIso (α .N-ob x)

  isPshEquiv : PshHom P Q → Type _
  isPshEquiv α = ∀ x → isEquiv (α .N-ob x)

  isPropIsPshIso : ∀ {α} → isProp (isPshIso α)
  isPropIsPshIso = isPropΠ λ _ → isPropIsIsoSet (P .F-ob _ .snd) (Q .F-ob _ .snd)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  PshIsoΣ : Type _
  PshIsoΣ = Σ[ α ∈ PshHom P Q ] isPshIso {P = P}{Q = Q} α

  record PshIso : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    constructor pshiso
    field
      trans : PshHom P Q
      nIso : isPshIso {P = P}{Q = Q} trans

  PshIsoΣIso : Iso PshIso PshIsoΣ
  unquoteDef PshIsoΣIso = defineRecordIsoΣ PshIsoΣIso (quote (PshIso))

  Psh≃ : Type _
  Psh≃ = Σ[ α ∈ PshHom P Q ] isPshEquiv {P = P}{Q = Q} α

  open PshIso

  PshIso→PshIsoLift : PshIso → PshIsoLift C P Q
  PshIso→PshIsoLift α .NatIso.trans .NatTrans.N-ob x x₁ =
    lift (α .trans .N-ob x (x₁ .lower))
  PshIso→PshIsoLift α .NatIso.trans .NatTrans.N-hom f =
    funExt (λ x₁ → cong lift (α .trans .N-hom _ _ f (x₁ .lower)))
  PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.inv =
    λ z → lift (α .nIso x .fst (z .lower))
  PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.sec =
    funExt (λ x₁ → cong lift (α .nIso x .snd .fst (x₁ .lower)) )
  PshIso→PshIsoLift α .NatIso.nIso x .isIsoC.ret =
    funExt (λ x₁ → cong lift (α .nIso x .snd .snd (x₁ .lower)))

  record isPshIso' (α : PshHom' P Q ) : Type (ℓ-max ℓc (ℓ-max ℓp ℓq)) where
    no-eta-equality
    field
      nIso : ∀ c → isIso (α .PshHom'.N-ob c)

  record isPshIsoEq (α : PshHomEq P Q ) : Type (ℓ-max ℓc (ℓ-max ℓp ℓq)) where
    no-eta-equality
    field
      nIso : ∀ c → isIso (α .PshHomEq.N-ob c)

  record PshIso' : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    no-eta-equality
    field
      isos : ∀ c → Iso P.p[ c ] Q.p[ c ]
      nat  : ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ])
        → PathEq (isos c .Iso.fun (f P.⋆ p))
                 (f Q.⋆ isos c' .Iso.fun p)
    toPshHom' : PshHom' P Q
    toPshHom' .PshHom'.N-ob = λ c → isos c .Iso.fun
    toPshHom' .PshHom'.N-hom = nat

    PshIso'ToIsPshIso' : isPshIso' toPshHom'
    PshIso'ToIsPshIso' .isPshIso'.nIso c = IsoToIsIso (isos c)

  record PshIsoEq : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    no-eta-equality
    field
      isos : ∀ c → Iso P.p[ c ] Q.p[ c ]
      nat : ∀ c c' (f : C [ c , c' ]) (p' : P.p[ c' ]) (p : P.p[ c ]) →
        f P.⋆ p' Eq.≡ p
        → (f Q.⋆ isos c' .Iso.fun p') Eq.≡ (isos c .Iso.fun p)
    toPshHomEq : PshHomEq P Q
    toPshHomEq .PshHomEq.N-ob = λ c → isos c .Iso.fun
    toPshHomEq .PshHomEq.N-hom = nat

    PshIsoEqToIsPshIsoEq : isPshIsoEq toPshHomEq
    PshIsoEqToIsPshIsoEq .isPshIsoEq.nIso c = IsoToIsIso (isos c)

open PshIso

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq}
  where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  invPshIso : (α : PshIso P Q) → PshIso Q P
  invPshIso α .trans .N-ob c = α .nIso c .fst
  invPshIso α .trans .N-hom _ _ f q =
    sym (α .nIso _ .snd .snd _)
    ∙ cong (α .nIso _ .fst)
      (sym $
        α .trans .N-hom _ _ _ _
        ∙ Q.⟨ refl ⟩⋆⟨ α .nIso _ .snd .fst _ ⟩
        ∙ (sym $ α .nIso _ .snd .fst _))
    ∙ α .nIso _ .snd .snd _
  invPshIso α .nIso c .fst = α .trans .N-ob _
  invPshIso α .nIso c .snd .fst = α .nIso _ .snd .snd
  invPshIso α .nIso c .snd .snd = α .nIso _ .snd .fst

  -- PshIsoEq version of invPshIso
  invPshIsoEq : PshIsoEq P Q → PshIsoEq Q P
  invPshIsoEq α .PshIsoEq.isos c = invIso (α .PshIsoEq.isos c)
  invPshIsoEq α .PshIsoEq.nat c c' f q' q e =
    -- e : f Q.⋆ q' Eq.≡ q
    -- Goal: (f P.⋆ inv c' q') Eq.≡ (inv c q)
    -- Strategy: apply fun c to both sides, show they're equal, use isoFunInjective
    Eq.pathToEq $ isoFunInjective (α .PshIsoEq.isos c) _ _ $
      -- fun c (f P.⋆ inv c' q') ≡ fun c (inv c q)
      -- = f Q.⋆ fun c' (inv c' q') by naturality (sym)
      Eq.eqToPath (Eq.sym (α .PshIsoEq.nat c c' f _ _ Eq.refl))
      -- = f Q.⋆ q' by sec c'
      ∙ Q.⟨ refl ⟩⋆⟨ α .PshIsoEq.isos c' .Iso.sec q' ⟩
      -- = q by e
      ∙ Eq.eqToPath e
      -- = fun c (inv c q) by sym (sec c)
      ∙ sym (α .PshIsoEq.isos c .Iso.sec q)

  -- Convenient when we already have the iso on Types
  Isos→PshIso : (isos : ∀ x → Iso (P.p[ x ]) (Q.p[ x ]))
    → (∀ x y (f : C [ x , y ]) (p : P.p[ y ]) →
      Iso.fun (isos x) (f P.⋆ p) ≡ f Q.⋆ (Iso.fun (isos y) p))
    → PshIso P Q
  Isos→PshIso isos isos-areNat .trans .N-ob x = Iso.fun (isos x)
  Isos→PshIso isos isos-areNat .trans .N-hom = isos-areNat
  Isos→PshIso isos isos-areNat .nIso x .fst = Iso.inv (isos x)
  Isos→PshIso isos isos-areNat .nIso x .snd .fst = Iso.sec (isos x)
  Isos→PshIso isos isos-areNat .nIso x .snd .snd = Iso.ret (isos x)

  PshIso→Isos : PshIso P Q → ∀ x → Iso (P.p[ x ]) (Q.p[ x ])
  PshIso→Isos α = λ x →
    iso (α .trans .N-ob x) (α .nIso x .fst)
      (α .nIso x .snd .fst)
      (α .nIso x .snd .snd)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq}
  {α : PshHom P Q}{α⁻ : PshHom Q P}
  (ret : α ⋆PshHom α⁻ ≡ idPshHom)
  (sec : α⁻ ⋆PshHom α ≡ idPshHom)
  where

  -- TODO: make α, α⁻ explicit arguments
  makePshIso : PshIso P Q
  makePshIso .trans = α
  makePshIso .nIso c .fst q = α⁻ .N-ob c q
  makePshIso .nIso c .snd .fst q = funExt₂⁻ (cong N-ob sec) c q
  makePshIso .nIso c .snd .snd p = funExt₂⁻ (cong N-ob ret) c p

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq}
  (α : PshIso P Q)
  where

  PshIso→ret : α .trans ⋆PshHom invPshIso α .trans ≡ idPshHom {P = P}
  PshIso→ret =
    makePshHomPath (funExt₂ λ c p → α .nIso _ .snd .snd (idPshHom {C = C} {P = P} .N-ob c p))

  PshIso→sec :
    Path
      (PshHom Q Q)
      (invPshIso α .trans ⋆PshHom α .trans)
      idPshHom
  PshIso→sec =
    makePshHomPath (funExt₂ λ c p → α .nIso c .snd .fst p)

open PshHom
module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  makePshIsoΣPath : {α β : PshIsoΣ P Q} →
    α .fst .N-ob ≡ β .fst .N-ob → α ≡ β
  makePshIsoΣPath {α} {β} α≡β =
    Σ≡Prop
      (λ γ → isPropIsPshIso {C = C} {P = P} {Q = Q} {α = γ})
      (makePshHomPath α≡β)

  makePshIsoPath : {α β : PshIso P Q} →
    α .trans .N-ob ≡ β .trans .N-ob → α ≡ β
  makePshIsoPath {α} {β} N-ob≡ =
    isoFunInjective (PshIsoΣIso P Q) α β (makePshIsoΣPath N-ob≡)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓp) where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  open isUnivalent
  open isIsoC
  PshCatIso→PshIso : CatIso (PresheafCategory C ℓp) P Q → PshIso P Q
  PshCatIso→PshIso α .trans .N-ob = α .fst .NatTrans.N-ob
  PshCatIso→PshIso α .trans .N-hom x₁ y f p =
    funExt⁻ (α .fst .NatTrans.N-hom _) p
  PshCatIso→PshIso α .nIso x .fst = NatTrans.N-ob (α .snd .inv) x
  PshCatIso→PshIso α .nIso x .snd .fst =
    funExt⁻ (funExt⁻ (cong NatTrans.N-ob $ α .snd .sec) _)
  PshCatIso→PshIso α .nIso x .snd .snd =
    funExt⁻ (funExt⁻ (cong NatTrans.N-ob $ α .snd .ret) _)

  NatIso→PshIso : NatIso P Q → PshIso P Q
  NatIso→PshIso α .trans = NatTrans→PshHom (α .NatIso.trans)
  NatIso→PshIso α .nIso c .fst = α .NatIso.nIso c .inv
  NatIso→PshIso α .nIso c .snd .fst q = funExt⁻ (α .NatIso.nIso c .sec) q
  NatIso→PshIso α .nIso c .snd .snd p = funExt⁻ (α .NatIso.nIso c .ret) p

  PshIso→SETIso : PshIso P Q → ∀ x → CatIso (SET ℓp) (P .F-ob x) (Q .F-ob x)
  PshIso→SETIso α c .fst = α .trans .N-ob c
  PshIso→SETIso α c .snd .inv = α .nIso c .fst
  PshIso→SETIso α c .snd .sec = funExt (α .nIso c .snd .fst)
  PshIso→SETIso α c .snd .ret = funExt (α .nIso c .snd .snd)

  PshIso→NatIso : PshIso P Q → NatIso P Q
  PshIso→NatIso α .NatIso.trans = PshHom→NatTrans (α .trans)
  PshIso→NatIso α .NatIso.nIso c .inv = α .nIso c .fst
  PshIso→NatIso α .NatIso.nIso c .sec = funExt (α .nIso c .snd .fst)
  PshIso→NatIso α .NatIso.nIso c .ret = funExt (α .nIso c .snd .snd)

  PshIso→Path : PshIso P Q → P ≡ Q
  PshIso→Path α =
    Functor≡
      (λ c → CatIsoToPath isUnivalentSET' (PshIso→SETIso α c))
      λ {c}{c'} f →
        toPathP (funExt (λ q →
          (transport (Pc≡Qc c') $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
            ≡⟨ univSet'β (PshIso→SETIso α c') ((f P.⋆ transport (sym $ Pc≡Qc c) q)) ⟩
          (α .trans .N-ob c' $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
            ≡⟨ cong (α .trans .N-ob c') P.⟨ refl ⟩⋆⟨ ~univSet'β (PshIso→SETIso α c) q ⟩ ⟩
          (α .trans .N-ob c' $ f P.⋆ α .nIso c .fst q)
            ≡⟨ α .trans .N-hom c' c f (α .nIso c .fst q) ⟩
          f Q.⋆ (α .trans .N-ob c $ α .nIso c .fst q)
            ≡⟨ Q.⟨ refl ⟩⋆⟨ α .nIso c .snd .fst q ⟩ ⟩
          f Q.⋆ q
            ∎ ))
    where
      Pc≡Qc : ∀ c → P.p[ c ] ≡ Q.p[ c ]
      Pc≡Qc c i = ⟨ CatIsoToPath isUnivalentSET' (PshIso→SETIso α c) i ⟩

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where
  idPshIso : PshIso P P
  idPshIso .trans = idPshHom
  idPshIso .nIso _ = IsoToIsIso idIso

  idPshIso' : PshIso' P P
  idPshIso' .PshIso'.isos = λ _ → idIso
  idPshIso' .PshIso'.nat = idPshHom' {P = P} .PshHom'.N-hom

  idPshIsoEq : PshIsoEq P P
  idPshIsoEq .PshIsoEq.isos = λ _ → idIso
  idPshIsoEq .PshIsoEq.nat = idPshHomEq {P = P} .PshHomEq.N-hom

module _ {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} where
  seqIsPshIso : ∀ {α : PshHom P Q}{β : PshHom Q R}
    → isPshIso {P = P}{Q = Q} α
    → isPshIso {P = Q}{Q = R} β
    → isPshIso {P = P}{Q = R} (α ⋆PshHom β)
  seqIsPshIso {α}{β} αIsIso βIsIso x = IsoToIsIso $
    compIso (isIsoToIso (αIsIso x)) (isIsoToIso (βIsIso x))

  _⋆PshIso_ : PshIso P Q → PshIso Q R → PshIso P R
  (α ⋆PshIso β) .trans = α .trans ⋆PshHom β .trans
  (α ⋆PshIso β) .nIso x =
    IsoToIsIso $
      compIso (isIsoToIso (α .nIso x)) (isIsoToIso (β .nIso x))
  infixr 9 _⋆PshIso_

  _⋆PshIsoEq_ : PshIsoEq P Q → PshIsoEq Q R → PshIsoEq P R
  (α ⋆PshIsoEq β) .PshIsoEq.isos c = compIso (α .PshIsoEq.isos c) (β .PshIsoEq.isos c)
  (α ⋆PshIsoEq β) .PshIsoEq.nat = λ c c' f p' p z →
                                     β .PshIsoEq.nat c c' f (Iso.fun (α .PshIsoEq.isos c') p')
                                     (Iso.fun (α .PshIsoEq.isos c) p) (α .PshIsoEq.nat c c' f p' p z)
  infixr 9 _⋆PshIsoEq_

module _ {C : Category ℓc ℓc'} where
  step-PshIso : ∀ (P : Presheaf C ℓp) {Q : Presheaf C ℓq} {R : Presheaf C ℓr}
    → PshIso Q R → PshIso P Q → PshIso P R
  step-PshIso _ g f = f ⋆PshIso g

  infixr  2 step-PshIso
  syntax step-PshIso P Q f = P PshIso⟨ f ⟩ Q

  _∎PshIso : ∀ (P : Presheaf C ℓp) → PshIso P P
  P ∎PshIso = idPshIso {P = P}

  infix   3 _∎PshIso

module _ {C : Category ℓc ℓc'}{P Q : Presheaf C ℓp} (path : P ≡ Q) where
  pathToPshIso : PshIso P Q
  pathToPshIso = PshCatIso→PshIso _ _ (pathToIso path)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}
  where

  private
    module C = Category C
    module P = PresheafNotation P

  PQ-ob-ty = Eq.singl (P .F-ob)
  PQ-hom-ty : PQ-ob-ty → Type _
  PQ-hom-ty PQ-ob =
    Eq.singlP
      (Eq.ap
        (λ Q-ob → ∀ {x}{y} → C [ x , y ] → ⟨ Q-ob y ⟩ → ⟨ Q-ob x ⟩)
        (PQ-ob .snd))
      (P .F-hom)

  eqToPshIso-ob : (PQ-ob : PQ-ob-ty) →
    ∀ (c : C.ob) → hSet ℓp
  eqToPshIso-ob (_ , Eq.refl) = P .F-ob

  eqToPshIso-N-ob : (PQ-ob : PQ-ob-ty) →
    ∀ (c : C.ob) → P.p[ c ] → ⟨ PQ-ob .fst c ⟩
  eqToPshIso-N-ob (_ , Eq.refl) = λ _ z → z

  eqToPshIso-N-hom :
    (PQ-ob : PQ-ob-ty) →
    (PQ-hom : PQ-hom-ty PQ-ob) →
    ∀ (c c' : C.ob) → (f : C [ c , c' ]) →
    (p : P.p[ c' ]) →
    eqToPshIso-N-ob PQ-ob c (f P.⋆ p) ≡
      PQ-hom .fst f (eqToPshIso-N-ob PQ-ob c' p)
  eqToPshIso-N-hom (_ , Eq.refl) (_ , Eq.refl) =
    λ _ _ _ _ → refl

  eqToPshIso-nIso :
    (PQ-ob : PQ-ob-ty) →
    ∀ (c : C.ob) → isIso (eqToPshIso-N-ob PQ-ob c)
  eqToPshIso-nIso (_ , Eq.refl) c =
    (λ z → z) , (λ _ → refl) , (λ _ → refl)

  module _
    (Q : Presheaf C ℓp)
    (eq-ob : P .F-ob Eq.≡ Q .F-ob)
    (eq-hom :
      Eq.HEq
        (Eq.ap (λ F-ob' → ∀ {x}{y} →
                 C [ x , y ] → ⟨ F-ob' y ⟩ → ⟨ F-ob' x ⟩) eq-ob)
        (P .F-hom) (Q .F-hom))
    where

    private
      PQ-ob : PQ-ob-ty
      PQ-ob = _ , eq-ob

      PQ-hom : PQ-hom-ty PQ-ob
      PQ-hom = _ , eq-hom

    eqToPshHom : PshHom P Q
    eqToPshHom = record {
          N-ob = eqToPshIso-N-ob PQ-ob
        ; N-hom = eqToPshIso-N-hom PQ-ob PQ-hom }

    eqToPshIso : PshIso P Q
    eqToPshIso = record {
        trans = eqToPshHom
      ; nIso = eqToPshIso-nIso PQ-ob}

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp} where
  pathToPshIsoRefl : pathToPshIso (refl {x = P}) ≡ idPshIso
  pathToPshIsoRefl = makePshIsoPath $ funExt λ _ → funExt λ x →
    transportTransport⁻
      (λ i → P .F-ob (transp (λ j → ob C) i _) .fst)
      x

-- Whiskering
module _
  {C : Category ℓc ℓc'}
  {D : Category ℓd ℓd'}
  {P : Presheaf D ℓp}
  {Q : Presheaf D ℓq}
  where
  _∘ˡ_ : (α : PshHom P Q) (F : Functor C D)
    → PshHom (P ∘F (F ^opF)) (Q ∘F (F ^opF))
  (α ∘ˡ F) .N-ob x = α .N-ob (F ⟅ x ⟆)
  (α ∘ˡ F) .N-hom x y f p = α .N-hom _ _ _ p

  _∘ˡⁱ_ : (α : PshIso P Q) (F : Functor C D)
    → PshIso (P ∘F (F ^opF)) (Q ∘F (F ^opF))
  (α ∘ˡⁱ F) .trans = α .trans ∘ˡ F
  (α ∘ˡⁱ F) .nIso x .fst = α .nIso _ .fst
  (α ∘ˡⁱ F) .nIso x .snd .fst = α .nIso _ .snd .fst
  (α ∘ˡⁱ F) .nIso x .snd .snd = α .nIso _ .snd .snd

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp)
  where
  private
    module P = PresheafNotation P

  precomp𝟙PshIso : PshIso P (P ∘F (𝟙⟨ C ⟩ ^opF))
  precomp𝟙PshIso = eqToPshIso _ Eq.refl Eq.refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  (α : PshHom P Q)
  where
  ⋆PshHomIdL : idPshHom {P = P} ⋆PshHom α ≡ α
  ⋆PshHomIdL = makePshHomPath refl
  ⋆PshHomIdR : α ⋆PshHom idPshHom ≡ α
  ⋆PshHomIdR = makePshHomPath refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  {R : Presheaf C ℓr} {S : Presheaf C ℓs}
  (α : PshHom P Q)(β : PshHom Q R)(γ : PshHom R S)
  where

  ⋆PshHomAssoc :
    Path
      (PshHom P S)
      ((α ⋆PshHom β) ⋆PshHom γ)
      (α ⋆PshHom (β ⋆PshHom γ))
  ⋆PshHomAssoc = makePshHomPath refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  (α : PshHomEq P Q)
  where
  ⋆PshHomEqIdL : idPshHomEq {P = P} ⋆PshHomEq α ≡ α
  ⋆PshHomEqIdL = refl
  ⋆PshHomEqIdR : α ⋆PshHomEq idPshHomEq ≡ α
  ⋆PshHomEqIdR = refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp} {Q : Presheaf C ℓq}
  {R : Presheaf C ℓr} {S : Presheaf C ℓs}
  (α : PshHomEq P Q)(β : PshHomEq Q R)(γ : PshHomEq R S)
  where
  ⋆PshHomEqAssoc :
    Path
      (PshHomEq P S)
      ((α ⋆PshHomEq β) ⋆PshHomEq γ)
      (α ⋆PshHomEq (β ⋆PshHomEq γ))
  ⋆PshHomEqAssoc = refl

module _
  {C : Category ℓc ℓc'}
  {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} where

  postcomp⋆PshHom-Iso : (α : PshIso Q R) → Iso (PshHom P Q) (PshHom P R)
  postcomp⋆PshHom-Iso α .Iso.fun β = β ⋆PshHom α .trans
  postcomp⋆PshHom-Iso α .Iso.inv β = β ⋆PshHom invPshIso α .trans
  postcomp⋆PshHom-Iso α .Iso.sec β =
    ⋆PshHomAssoc _ _ _
    ∙ cong (β ⋆PshHom_) (PshIso→sec α)
    ∙ ⋆PshHomIdR β
  postcomp⋆PshHom-Iso α .Iso.ret β =
    ⋆PshHomAssoc _ _ _
    ∙ cong (β ⋆PshHom_) (PshIso→ret α)
    ∙ ⋆PshHomIdR β

  precomp⋆PshHom-Iso : (α : PshIso P Q) → Iso (PshHom Q R) (PshHom P R)
  precomp⋆PshHom-Iso α .Iso.fun β = α .trans ⋆PshHom β
  precomp⋆PshHom-Iso α .Iso.inv β = invPshIso α .trans ⋆PshHom β
  precomp⋆PshHom-Iso α .Iso.sec β =
    sym (⋆PshHomAssoc _ _ _)
    ∙ cong (_⋆PshHom β) (PshIso→ret α)
    ∙ ⋆PshHomIdL β
  precomp⋆PshHom-Iso α .Iso.ret β =
    sym (⋆PshHomAssoc _ _ _)
    ∙ cong (_⋆PshHom β) (PshIso→sec α)
    ∙ ⋆PshHomIdL β

module _ {C : Category ℓc ℓc'} {P : Presheaf C ℓp} {Q : Presheaf C ℓq} where
  module _ (α : PshHom P Q) (α' : singl (α .N-ob)) where
    α'-N-hom-ty : PshHom-N-hom-ty P Q (α' .fst)
    α'-N-hom-ty = subst (PshHom-N-hom-ty P Q) (α' .snd) (α .N-hom)

    improvePshHom : PshHom P Q
    improvePshHom .N-ob =  α' .fst
    improvePshHom .N-hom =  α'-N-hom-ty

  module _ (α : PshIso P Q) (α' : singl (α .trans .N-ob)) (α⁻ : singl (invPshIso α .trans .N-ob)) where
    isInvα⁻ : ∀ (x : C .ob)
      → section (α' .fst x) (α⁻ .fst x) × retract (α' .fst x) (α⁻ .fst x)
    isInvα⁻ x =
      subst2 (λ N-ob N-ob⁻ → section (N-ob x) (N-ob⁻ x) × retract (N-ob x) (N-ob⁻ x))
        (α' .snd)
        (α⁻ .snd)
        (α .nIso x .snd)
    improvePshIso : PshIso P Q
    improvePshIso .trans = improvePshHom (α .trans) α'
    improvePshIso .nIso x = (α⁻ .fst x) , isInvα⁻ x

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp) where
  yo≅PshHomPsh :
    PshIso (yo {C = PresheafCategory C ℓp} P) (PshHomPsh {ℓp = ℓp} P)
  yo≅PshHomPsh .trans .N-ob c = NatTrans→PshHom
  yo≅PshHomPsh .trans .N-hom c c' f p = makePshHomPath refl
  yo≅PshHomPsh .nIso Q .fst = PshHom→NatTrans
  yo≅PshHomPsh .nIso Q .snd .fst _ = makePshHomPath refl
  yo≅PshHomPsh .nIso Q .snd .snd _ = makeNatTransPath refl

PSHHOMCAT : (C : Category ℓc ℓc') (ℓp : Level) → Category (ℓ-max (ℓ-max ℓc ℓc') (ℓ-suc ℓp)) (ℓ-max (ℓ-max ℓc ℓc') ℓp)
PSHHOMCAT C ℓp .ob = Presheaf C ℓp
PSHHOMCAT C ℓp .Hom[_,_] = PshHom
PSHHOMCAT C ℓp .id = idPshHom
PSHHOMCAT C ℓp ._⋆_ = _⋆PshHom_
PSHHOMCAT C ℓp .⋆IdL = λ α → makePshHomPath refl
PSHHOMCAT C ℓp .⋆IdR = λ α → makePshHomPath refl
PSHHOMCAT C ℓp .⋆Assoc = λ α β γ → makePshHomPath refl
PSHHOMCAT C ℓp .isSetHom = isSetPshHom _ _

PRESHEAFEQ : (C : Category ℓc ℓc') (ℓp : Level) → Category (ℓ-max (ℓ-max ℓc ℓc') (ℓ-suc ℓp)) (ℓ-max (ℓ-max ℓc ℓc') ℓp)
PRESHEAFEQ C ℓP .ob = Presheaf C ℓP
PRESHEAFEQ C ℓP .Hom[_,_] = PshHomEq
PRESHEAFEQ C ℓP .id = idPshHomEq
PRESHEAFEQ C ℓP ._⋆_ = _⋆PshHomEq_
PRESHEAFEQ C ℓP .⋆IdL = ⋆PshHomEqIdL
PRESHEAFEQ C ℓP .⋆IdR = ⋆PshHomEqIdR
PRESHEAFEQ C ℓP .⋆Assoc = ⋆PshHomEqAssoc
PRESHEAFEQ C ℓP .isSetHom = isSetPshHomEq _ _
