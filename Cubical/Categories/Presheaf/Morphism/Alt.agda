{- This is intended to replace Presheaf.Morphism upstream -}
module Cubical.Categories.Presheaf.Morphism.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.More
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure

open import Cubical.Functions.FunExtEquiv

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More
open import Cubical.Data.Sigma
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Limits
open import Cubical.Categories.LocallySmall
  using (module LocallySmallCategoryNotation;  LocallySmallCategoryᴰ; module LocallySmallCategoryᴰNotation; LEVELω; LEVELω-iso; mapω'; liftω)
import Cubical.Categories.LocallySmall as LocallySmall
open import Cubical.Categories.NaturalTransformation hiding (_∘ˡ_; _∘ˡⁱ_)
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Profunctor.General

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
open Functor
open isUnivalent
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

  -- Natural transformation between presheaves of different levels
  record PshHom : Type (ℓ-max (ℓ-max ℓc ℓc') (ℓ-max ℓp ℓq)) where
    no-eta-equality
    constructor pshhom
    field
      N-ob : ∀ (c : C.ob) → P.p[ c ] → Q.p[ c ]
      N-hom : ∀ c c' (f : C [ c , c' ]) (p : P.p[ c' ]) →
        N-ob c (f P.⋆ p) ≡ (f Q.⋆ N-ob c' p)

  PshHomΣIso : Iso PshHom PshHomΣ
  unquoteDef PshHomΣIso = defineRecordIsoΣ PshHomΣIso (quote (PshHom))

  isSetPshHom : isSet PshHom
  isSetPshHom = isOfHLevelRetractFromIso 2 PshHomΣIso isSetPshHomΣ

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

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}where
  idPshHom : PshHom P P
  idPshHom .N-ob x z = z
  idPshHom .N-hom x y f p = refl

module _ {C : Category ℓc ℓc'} where
  _⋆PshHom_ : ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓr} →
    PshHom P Q → PshHom Q R → PshHom P R
  (α ⋆PshHom β) .N-ob x p = β .N-ob x (α .N-ob x p)
  (α ⋆PshHom β) .N-hom x y f p =
    cong (β .N-ob _) (α .N-hom x y f p)
    ∙ β .N-hom x y f (α .N-ob y p)

  _⋆PshHomNatTrans_ :
    ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓq}{R : Presheaf C ℓq} →
      PshHom P Q → NatTrans Q R → PshHom P R
  α ⋆PshHomNatTrans β = α ⋆PshHom NatTrans→PshHom β
  _⋆NatTransPshHom_ :
    ∀ {P : Presheaf C ℓp}{Q : Presheaf C ℓp}{R : Presheaf C ℓr} →
      NatTrans P Q → PshHom Q R → PshHom P R
  α ⋆NatTransPshHom β = NatTrans→PshHom α ⋆PshHom β

-- TODO:
--   should be able to rewrite this as LocallySmallNatTransᴰ
PRESHEAF : ∀ (C : Category ℓc ℓc')
  → LocallySmallCategoryᴰ LEVELω (mapω' (Presheaf C))
PRESHEAF C .LocallySmallCategoryᴰ.Hom-ℓᴰ = _
PRESHEAF C .LocallySmallCategoryᴰ.Hom[_][_,_] _ (liftω P) (liftω Q) = PshHom P Q
PRESHEAF C .LocallySmallCategoryᴰ.idᴰ = idPshHom
PRESHEAF C .LocallySmallCategoryᴰ._⋆ᴰ_  = _⋆PshHom_
PRESHEAF C .LocallySmallCategoryᴰ.⋆IdLᴰ = λ _ → makePshHomPath refl
PRESHEAF C .LocallySmallCategoryᴰ.⋆IdRᴰ = λ _ → makePshHomPath refl
PRESHEAF C .LocallySmallCategoryᴰ.⋆Assocᴰ = λ _ _ _ → makePshHomPath refl
PRESHEAF C .LocallySmallCategoryᴰ.isSetHomᴰ = isSetPshHom _ _

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

{- a PshIso is a PshHom whose underlying functions are iso -}
module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  isPshIso : PshHom P Q → Type _
  isPshIso α = ∀ x → isIso (α .N-ob x)

  isPropIsPshIso : ∀ {α} → isProp (isPshIso α)
  isPropIsPshIso = isPropΠ λ _ → isPropIsIsoSet (P .F-ob _ .snd) (Q .F-ob _ .snd)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq) where
  private
    module P = PresheafNotation P using (p[_])
    module Q = PresheafNotation Q using (p[_])
  PshIsoΣ : Type _
  PshIsoΣ = Σ[ α ∈ PshHom P Q ] isPshIso {P = P}{Q = Q} α

  record PshIso : Type (ℓ-max (ℓ-max ℓp ℓq) (ℓ-max ℓc ℓc')) where
    constructor pshiso
    field
      trans : PshHom P Q
      nIso : isPshIso {P = P}{Q = Q} trans

  PshIsoΣIso : Iso PshIso PshIsoΣ
  unquoteDef PshIsoΣIso = defineRecordIsoΣ PshIsoΣIso (quote (PshIso))

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

open PshIso

module _ {C : Category ℓc ℓc'} where
  private
    module LEVELω = LocallySmallCategoryNotation LEVELω
    PshC = PRESHEAF C
    module PshC = LocallySmallCategoryᴰNotation PshC

  module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    makePshIsoPath : {α β : PshIso P Q}
      → α .trans .N-ob ≡ β .trans .N-ob
      → α ≡ β
    makePshIsoPath α≡β = isoFunInjective (PshIsoΣIso P Q) _ _
      (Σ≡Prop (λ α → isPropIsPshIso {α = α}) (makePshHomPath α≡β))

    invPshIso : PshIso P Q → PshIso Q P
    invPshIso α .trans .N-ob c = α .nIso c .fst
    invPshIso α .trans .N-hom c c' f p =
      isoFun≡ (invIso (isIsoToIso (α .nIso _)))
        (Q.⟨⟩⋆⟨ sym $ α .nIso c' .snd .fst p ⟩ ∙ sym (α .trans .N-hom _ _ _ _))
    invPshIso α .nIso x .fst = α .trans .N-ob x
    invPshIso α .nIso x .snd .fst = α .nIso x .snd .snd
    invPshIso α .nIso x .snd .snd = α .nIso x .snd .fst

    PshIso→PshCatIso : PshIso P Q
      → PshC.ISOCᴰ.Hom[ LEVELω-iso ][ liftω P , liftω Q ]
    PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.funᴰ = α .trans
    PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.invᴰ = invPshIso α .trans
    PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.secᴰ =
      ΣPathP (refl , makePshHomPath (funExt λ x → funExt (α .nIso x .snd .fst)))
    PshIso→PshCatIso α .LocallySmall.CatIsoᴰ.retᴰ =
      ΣPathP (refl , makePshHomPath (funExt λ x → funExt (α .nIso x .snd .snd)))

    PshCatIso→PshIso
      : PshC.ISOCᴰ.Hom[ LEVELω-iso ][ liftω P , liftω Q ]
      → PshIso P Q
    PshCatIso→PshIso α .trans = α .LocallySmall.CatIsoᴰ.funᴰ
    PshCatIso→PshIso α .nIso x .fst = α .LocallySmall.CatIsoᴰ.invᴰ .N-ob x
    PshCatIso→PshIso α .nIso x .snd .fst q i = α .LocallySmall.CatIsoᴰ.secᴰ i .snd .N-ob x q
    PshCatIso→PshIso α .nIso x .snd .snd p i = α .LocallySmall.CatIsoᴰ.retᴰ i .snd .N-ob x p

    PshIso≅PshCatIso :
      Iso (PshIso P Q)
          PshC.ISOCᴰ.Hom[ LEVELω-iso ][ liftω P , liftω Q ]
    PshIso≅PshCatIso .Iso.fun = PshIso→PshCatIso
    PshIso≅PshCatIso .Iso.inv = PshCatIso→PshIso
    PshIso≅PshCatIso .Iso.rightInv α =
      PshC.ISOCᴰ.rectify (PshC.ISOCᴰ.≡out $ PshC.ISOCᴰ≡ refl)
    PshIso≅PshCatIso .Iso.leftInv α = makePshIsoPath refl

  -- This is for when they have the same universe level
  module _ {P : Presheaf C ℓp}{Q : Presheaf C ℓp} where
    private
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    PshIso→SETIso : PshIso P Q → ∀ x → CatIso (SET ℓp) (P .F-ob x) (Q .F-ob x)
    PshIso→SETIso α c .fst = α .trans .N-ob c
    PshIso→SETIso α c .snd .isIsoC.inv = α .nIso c .fst
    PshIso→SETIso α c .snd .isIsoC.sec = funExt (α .nIso c .snd .fst)
    PshIso→SETIso α c .snd .isIsoC.ret = funExt (α .nIso c .snd .snd)

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
-- module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓp) where
--   private
--     module P = PresheafNotation P
--     module Q = PresheafNotation Q
--   open isIsoC
--   PshCatIso→PshIso : CatIso (PresheafCategory C ℓp) P Q → PshIso P Q
--   PshCatIso→PshIso α .trans .N-ob = α .fst .NatTrans.N-ob
--   PshCatIso→PshIso α .trans .N-hom x₁ y f p =
--     funExt⁻ (α .fst .NatTrans.N-hom _) p
--   PshCatIso→PshIso α .nIso x .fst = NatTrans.N-ob (α .snd .inv) x
--   PshCatIso→PshIso α .nIso x .snd .fst =
--     funExt⁻ (funExt⁻ (cong NatTrans.N-ob $ α .snd .sec) _)
--   PshCatIso→PshIso α .nIso x .snd .snd =
--     funExt⁻ (funExt⁻ (cong NatTrans.N-ob $ α .snd .ret) _)

--   NatIso→PshIso : NatIso P Q → PshIso P Q
--   NatIso→PshIso α .trans = NatTrans→PshHom (α .NatIso.trans)
--   NatIso→PshIso α .nIso c .fst = α .NatIso.nIso c .inv
--   NatIso→PshIso α .nIso c .snd .fst q = funExt⁻ (α .NatIso.nIso c .sec) q
--   NatIso→PshIso α .nIso c .snd .snd p = funExt⁻ (α .NatIso.nIso c .ret) p

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

-- module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp} where
--   pathToPshIsoRefl : pathToPshIso (refl {x = P}) ≡ idPshIso
--   pathToPshIsoRefl = makePshIsoPath $ funExt λ _ → funExt λ x →
--     transportTransport⁻
--       (λ i → P .F-ob (transp (λ j → ob C) i _) .fst)
--       x

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
module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D)
         (P : Presheaf C ℓp)
         (Q : Presheaf D ℓq) where
  -- We define the displayed morphism by reindexing the codomain
  PshHet : Type (ℓ-max (ℓ-max (ℓ-max ℓc ℓc') ℓp) ℓq)
  PshHet = PshHom P (Q ∘F (F ^opF))

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         (F : Functor C D) (c : C .ob) where
  Functor→PshHet : PshHet F (C [-, c ]) (D [-, F ⟅ c ⟆ ])
  Functor→PshHet .N-ob = λ x → F .F-hom
  Functor→PshHet .N-hom = λ x y → F .F-seq

module _ {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
         {F : Functor C D}
         {P : Presheaf C ℓp}
         {Q : Presheaf D ℓq}
         (Fᴰ : PshHet F P Q)
         where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  ∫F : Functor (∫ᴾ P) (∫ᴾ Q)
  ∫F .F-ob (c , p) = F ⟅ c ⟆ , Fᴰ .N-ob c p
  ∫F .F-hom (f , tri) = (F ⟪ f ⟫) ,
    (sym $ Fᴰ .N-hom _ _ _ _)
    ∙ cong (Fᴰ .N-ob _) tri
  ∫F .F-id = Σ≡Prop (λ _ → Q.isSetPsh _ _) (F .F-id)
  ∫F .F-seq (f , _) (g , _) = Σ≡Prop (λ _ → Q.isSetPsh _ _) (F .F-seq f g)

  becomesUniversal :
    ∀ (v : C .ob) (e : P.p[ v ]) → Type _
  becomesUniversal v e = isUniversal D Q (F ⟅ v ⟆) (Fᴰ .N-ob _ e)

  becomesUniversal→UniversalElement :
    ∀ {v e}
    → becomesUniversal v e
    → UniversalElement D Q
  becomesUniversal→UniversalElement becomesUE .vertex = _
  becomesUniversal→UniversalElement becomesUE .element = _
  becomesUniversal→UniversalElement becomesUE .universal = becomesUE

  preservesUniversalElement : UniversalElement C P → Type _
  preservesUniversalElement ue =
    becomesUniversal (ue .vertex) (ue .element)

  preservesUniversalElements : Type _
  preservesUniversalElements = ∀ ue → preservesUniversalElement ue

  preservesUniversalElement→UniversalElement :
    (ue : UniversalElement C P)
    → preservesUniversalElement ue
    → UniversalElement D Q
  preservesUniversalElement→UniversalElement ue presUniversality =
    becomesUniversal→UniversalElement presUniversality

  -- If a presheaf preserves any universal element then it preserves
  -- all of them since universal elements are unique up to unique
  -- isomorphism. This is for free if the category is univalent
  -- because in that case UniversalElement C P is a Prop.

  -- This lemma, like other applications of Yoneda should be taken as
  -- an indication that it is probably fine to build the library
  -- around the seemingly weaker notion of preservesUniversalElement
  -- and push uses of this lemma to users rather than to pervasively
  -- use this in the library itself. YMMV
  preservesUniversalElement→PreservesUniversalElements :
    ∀ ue → preservesUniversalElement ue → preservesUniversalElements
  preservesUniversalElement→PreservesUniversalElements ue preservesUE ue' =
    isTerminalToIsUniversal D Q $
      preserveAnyTerminal→PreservesTerminals
        (∫ᴾ P)
        (∫ᴾ Q)
        ∫F
        (universalElementToTerminalElement C P ue)
        (isUniversalToIsTerminal D Q _ _ preservesUE)
        (universalElementToTerminalElement C P ue')

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp)
  where
  private
    module P = PresheafNotation P

  precomp𝟙PshIso : PshIso P (P ∘F (𝟙⟨ C ⟩ ^opF))
  precomp𝟙PshIso = eqToPshIso _ Eq.refl Eq.refl
