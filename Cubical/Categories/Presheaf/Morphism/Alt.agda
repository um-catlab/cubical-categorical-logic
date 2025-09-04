{- This is intended to replace Presheaf.Morphism upstream -}
module Cubical.Categories.Presheaf.Morphism.Alt where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.RecordEquiv.More
open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Isomorphism
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
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
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr : Level

open Category
open Contravariant
open Functor
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
