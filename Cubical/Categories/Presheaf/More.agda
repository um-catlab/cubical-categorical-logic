{-# OPTIONS --lossy-unification #-}
-- TODO: re-org this and upstream it
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport hiding (pathToIso)
open import Cubical.Data.Sigma

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Constructions.Lift
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Yoneda

open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Isomorphism.More

open Functor

private
  variable
    ℓ ℓ' ℓS ℓS' ℓS'' : Level
    ℓD ℓD' : Level

𝓟o = Presheaf

𝓟* : Category ℓ ℓ' → (ℓS : Level) → Type (ℓ-max (ℓ-max ℓ ℓ') (ℓ-suc ℓS))
𝓟* C ℓS = Functor C (SET ℓS)

module _ (C : Category ℓ ℓ') (c : C .Category.ob) where
  open Category
  open UniversalElement

  selfUnivElt :  UniversalElement C (C [-, c ])
  selfUnivElt .vertex = c
  selfUnivElt .element = C .id
  selfUnivElt .universal A = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdR)
    (C .⋆IdR))

  selfUnivEltᵒᵖ : UniversalElement (C ^op) (C [ c ,-])
  selfUnivEltᵒᵖ .vertex = c
  selfUnivEltᵒᵖ .element = C .id
  selfUnivEltᵒᵖ .universal _ = isoToIsEquiv (iso _ (λ z → z)
    (C .⋆IdL)
    (C .⋆IdL))

module _ {ℓo}{ℓh}{ℓp} (C : Category ℓo ℓh) (P : Presheaf C ℓp) where
  open UniversalElement
  open Category
  UniversalElementOn : C .ob → Type (ℓ-max (ℓ-max ℓo ℓh) ℓp)
  UniversalElementOn vertex =
    Σ[ element ∈ (P ⟅ vertex ⟆) .fst ] isUniversal C P vertex element

  UniversalElementToUniversalElementOn :
    (ue : UniversalElement C P) → UniversalElementOn (ue .vertex)
  UniversalElementToUniversalElementOn ue .fst = ue .element
  UniversalElementToUniversalElementOn ue .snd = ue .universal

module PresheafNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} (P : Presheaf C ℓp)
       where
  private
    module C = Category C
  p[_] : C.ob → Type ℓp
  p[ x ] = ⟨ P ⟅ x ⟆ ⟩

  _⋆_ : ∀ {x y} (f : C [ x , y ]) (g : p[ y ]) → p[ x ]
  f ⋆ g = P .F-hom f g

  ⋆IdL : ∀ {x} (g : p[ x ]) → C.id ⋆ g ≡ g
  ⋆IdL = funExt⁻ (P .F-id)

  ⋆Assoc : ∀ {x y z} (f : C [ x , y ])(g : C [ y , z ])(h : p[ z ]) →
    (f C.⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h)
  ⋆Assoc f g = funExt⁻ (P .F-seq g f)

  ⟨_⟩⋆⟨_⟩ : ∀ {x y} {f f' : C [ x , y ]} {g g' : p[ y ]}
            → f ≡ f' → g ≡ g' → f ⋆ g ≡ f' ⋆ g'
  ⟨ f≡f' ⟩⋆⟨ g≡g' ⟩ = cong₂ _⋆_ f≡f' g≡g'

  ⟨⟩⋆⟨_⟩ : ∀ {x y} {f : C [ x , y ]} {g g' : p[ y ]}
            → g ≡ g' → f ⋆ g ≡ f ⋆ g'
  ⟨⟩⋆⟨_⟩ = ⟨ refl ⟩⋆⟨_⟩

  ⟨_⟩⋆⟨⟩ : ∀ {x y} {f f' : C [ x , y ]} {g : p[ y ]}
            → f ≡ f' → f ⋆ g ≡ f' ⋆ g
  ⟨_⟩⋆⟨⟩ = ⟨_⟩⋆⟨ refl ⟩

  isSetPsh : ∀ {x} → isSet (p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd

-- TODO: move this stuff to Presheaf.Morphism.Alt and Presheaf.Representable.More
-- Natural transformation between presheaves of different levels
module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS') where
  private
    module C = Category C
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  -- TODO: make into a record
  PshHom : Type _
  PshHom = Σ[ α ∈ (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ]) ]
    (∀ x y (f : C [ x , y ]) (p : P.p[ y ]) →
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))

  isPropN-hom : ∀ (α : (∀ (x : C.ob) → P.p[ x ] → Q.p[ x ])) →
    isProp (∀ x y (f : C [ x , y ]) (p : P.p[ y ])→
     α x (f P.⋆ p) ≡ (f Q.⋆ α y p))
  isPropN-hom = λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ → Q.isSetPsh _ _

  isSetPshHom : isSet PshHom
  isSetPshHom = isSetΣ (isSetΠ (λ _ → isSet→ Q.isSetPsh)) λ _ → isProp→isSet (isPropN-hom _)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  makePshHomPath : ∀ {α β : PshHom P Q} → α .fst ≡ β .fst
   → α ≡ β
  makePshHomPath = ΣPathPProp (isPropN-hom P Q)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}where
  idPshHom : PshHom P P
  idPshHom .fst x z = z
  idPshHom .snd x y f p = refl

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'}{R : Presheaf C ℓS''} where
  _⋆PshHom_ : PshHom P Q → PshHom Q R → PshHom P R
  (α ⋆PshHom β) .fst x p = β .fst x (α .fst x p)
  (α ⋆PshHom β) .snd x y f p =
    cong (β .fst _) (α .snd x y f p)
    ∙ β .snd x y f (α .fst y p)

module _ {C : Category ℓ ℓ'} (P : Presheaf C ℓS) where
  private
    module C = Category C
    module P = PresheafNotation P
  -- Universe-polymorphic Yoneda recursion principle
  yoRec : ∀ {c} → P.p[ c ] → PshHom (C [-, c ]) P
  yoRec p .fst Γ f = f P.⋆ p
  yoRec p .snd Δ Γ γ f = P.⋆Assoc γ f p

  yoRecβ : ∀ {c}{p : P.p[ c ]} → yoRec p .fst _ C.id ≡ p
  yoRecβ = P.⋆IdL _

  yoRecη-elt : ∀ {c}(α : PshHom (C [-, c ]) P){Γ}{f : C [ Γ , c ]}
    → α .fst Γ f ≡ yoRec (α .fst _ C.id) .fst Γ f
  yoRecη-elt α =
    cong (α .fst _) (sym $ C.⋆IdR _)
    ∙ α .snd _ _ _ _

  yoRecη : ∀ {c}{α : PshHom (C [-, c ]) P}
    → α ≡ yoRec (α .fst _ C.id)
  yoRecη {α = α} = makePshHomPath (funExt (λ _ → funExt (λ _ → yoRecη-elt α)))

  IsoYoRec : ∀ c → Iso P.p[ c ] (PshHom (C [-, c ]) P)
  IsoYoRec c =
    iso yoRec (λ α → α .fst c C.id) (λ _ → sym $ yoRecη) (λ _ → yoRecβ)

  yoRec≡ : ∀ {c} {p : P.p[ c ]}{α}
    → p ≡ α .fst _ C.id
    → yoRec p ≡ α
  yoRec≡ = isoFun≡ (IsoYoRec _)


module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS')(α : PshHom P Q) where
  private
    module P = PresheafNotation P
    module C = Category C

  yoRec-natural-elt : ∀ {Γ c}{f : C [ Γ , c ]}{p : P.p[ c ]}
    → α .fst _ (yoRec P p .fst _ f) ≡ yoRec Q (α .fst c p) .fst Γ f
  yoRec-natural-elt = α .snd _ _ _ _

  yoRec-natural : ∀ {c}{p : P.p[ c ]} → (yoRec P p) ⋆PshHom α ≡ yoRec Q (α .fst c p)
  yoRec-natural = makePshHomPath $ funExt λ _ → funExt λ _ → yoRec-natural-elt

{- a PshIso is a PshHom whose underlying functions are iso -}
module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  isPshIso : PshHom P Q → Type _
  isPshIso α = ∀ x → isIso (α .fst x)

  isPropIsPshIso : ∀ {α} → isProp (isPshIso α)
  isPropIsPshIso = isPropΠ λ _ → isPropIsIsoSet (P .F-ob _ .snd) (Q .F-ob _ .snd)

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS') where
  private
    module P = PresheafNotation P using (p[_])
    module Q = PresheafNotation Q using (p[_])
  PshIso : Type _
  PshIso = Σ[ α ∈ PshHom P Q ] isPshIso {P = P}{Q = Q} α

  open NatIso
  open NatTrans
  PshIso→PshIsoLift : PshIso → PshIsoLift C P Q
  PshIso→PshIsoLift α .trans .N-ob x x₁ = lift (α .fst .fst x (x₁ .lower))
  PshIso→PshIsoLift α .trans .N-hom f = funExt (λ x₁ → cong lift (α .fst .snd _ _ f (x₁ .lower)))
  PshIso→PshIsoLift α .nIso x .isIsoC.inv = λ z → lift (α .snd x .fst (z .lower))
  PshIso→PshIsoLift α .nIso x .isIsoC.sec = funExt (λ x₁ → cong lift (α .snd x .snd .fst (x₁ .lower)) )
  PshIso→PshIsoLift α .nIso x .isIsoC.ret = funExt (λ x₁ → cong lift (α .snd x .snd .snd (x₁ .lower)))

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  makePshIsoPath : ∀ {α β : PshIso P Q} → α .fst .fst ≡ β .fst .fst
   → α ≡ β
  makePshIsoPath α≡β = Σ≡Prop (λ _ → isPropIsPshIso) (makePshHomPath α≡β)

-- This should eventually be upstreamed to go in the UniversalElement
-- module itself
module UniversalElementNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} {P : Presheaf C ℓp}
       (ue : UniversalElement C P)
       where
  open Category
  open UniversalElement ue public
  open NatTrans
  open NatIso
  open Iso
  REPR : Representation C P
  REPR = universalElementToRepresentation C P ue

  unIntroNT : NatTrans (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
                       (LiftF {ℓ' = ℓh} ∘F P)
  unIntroNT = REPR .snd .trans

  introNI : NatIso (LiftF {ℓ' = ℓh} ∘F P) (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
  introNI = symNatIso (REPR .snd)

  universalIso : ∀ (c : C .ob) → Iso (C [ c , vertex ]) ⟨ P ⟅ c ⟆ ⟩
  universalIso c = equivToIso (_ , universal c)

  private
    module P = PresheafNotation P
    module C = Category C

  intro : ∀ {c} → P.p[ c ] → C [ c , vertex ]
  intro = universalIso _ .inv

  intro⟨_⟩ : ∀ {c} → {f g : P.p[ c ]} → f ≡ g → intro f ≡ intro g
  intro⟨ p ⟩ = cong intro p

  opaque
    β : ∀ {c} → {p : P.p[ c ]} → (intro p P.⋆ element) ≡ p
    β = universalIso _ .rightInv _

    η : ∀ {c} → {f : C [ c , vertex ]} → f ≡ intro (f P.⋆ element)
    η {f = f} = sym (universalIso _ .leftInv _)

    weak-η : C .id ≡ intro element
    weak-η = η ∙ intro⟨ P.⋆IdL _ ⟩

    extensionality : ∀ {c} → {f f' : C [ c , vertex ]}
                   → (f P.⋆ element) ≡ (f' P.⋆ element)
                   → f ≡ f'
    extensionality = isoFunInjective (universalIso _) _ _

    intro≡ : ∀ {c} → {p : P.p[ c ]}{f : C [ c , vertex ]}
      → p ≡ f P.⋆ element
      → intro p ≡ f
    intro≡ = isoInv≡ (universalIso _)

    intro-natural : ∀ {c' c} → {p : P.p[ c ]}{f : C [ c' , c ]}
                  → f C.⋆ intro p ≡ intro (f P.⋆ p)
    intro-natural = sym $ intro≡ $ P.⟨⟩⋆⟨ sym $ β ⟩ ∙ (sym $ P.⋆Assoc _ _ _)

  ⋆element-isPshIso : isPshIso (yoRec P element)
  ⋆element-isPshIso x = IsoToIsIso (universalIso _)

  asPshIso : PshIso (C [-, vertex ]) P
  asPshIso = (yoRec P element) , ⋆element-isPshIso


module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} (((α , α-natural) , αIsIso) : PshIso P Q) where
  private
    module Q = PresheafNotation Q
  invPshIso : PshIso Q P
  invPshIso .fst .fst x = αIsIso _ .fst
  invPshIso .fst .snd _ _ f q =
    sym (αIsIso _ .snd .snd _)
    ∙ cong (αIsIso _ .fst) (sym $
      α-natural _ _ _ _ ∙ Q.⟨ refl ⟩⋆⟨ αIsIso _ .snd .fst _ ⟩ ∙ (sym $ αIsIso _ .snd .fst _))
    ∙ (αIsIso _ .snd .snd _)
  invPshIso .snd x .fst = α _
  invPshIso .snd x .snd .fst = αIsIso _ .snd .snd
  invPshIso .snd x .snd .snd = αIsIso _ .snd .fst

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS) where
  private
    module P = PresheafNotation P
    module Q = PresheafNotation Q
  open isUnivalent

  open NatTrans
  open isIsoC
  PshCatIso→PshIso : CatIso (PresheafCategory C ℓS) P Q → PshIso P Q
  PshCatIso→PshIso α .fst .fst = α .fst .N-ob
  PshCatIso→PshIso α .fst .snd x₁ y f p = funExt⁻ (α .fst .N-hom _) p
  PshCatIso→PshIso α .snd x .fst = N-ob (α .snd .inv) x
  PshCatIso→PshIso α .snd x .snd .fst = funExt⁻ (funExt⁻ (cong N-ob $ α .snd .sec) _)
  PshCatIso→PshIso α .snd x .snd .snd = funExt⁻ (funExt⁻ (cong N-ob $ α .snd .ret) _)

  PshIso→SETIso : PshIso P Q → ∀ x → CatIso (SET ℓS) (P .F-ob x) (Q .F-ob x)
  PshIso→SETIso α c .fst = α .fst .fst c
  PshIso→SETIso α c .snd .inv = α .snd c .fst
  PshIso→SETIso α c .snd .sec = funExt (α .snd c .snd .fst)
  PshIso→SETIso α c .snd .ret = funExt (α .snd c .snd .snd)

  PshIso→Path : PshIso P Q → P ≡ Q
  PshIso→Path α =
    Functor≡
      (λ c → CatIsoToPath isUnivalentSET' (PshIso→SETIso α c))
      λ {c}{c'} f →
        toPathP (funExt (λ q →
          (transport (Pc≡Qc c') $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
            ≡⟨ univSet'β (PshIso→SETIso α c') ((f P.⋆ transport (sym $ Pc≡Qc c) q)) ⟩
          (α .fst .fst c' $ (f P.⋆ transport (sym $ Pc≡Qc c) q))
            ≡⟨ cong (α .fst .fst c') P.⟨ refl ⟩⋆⟨ ~univSet'β (PshIso→SETIso α c) q ⟩ ⟩
          (α .fst .fst c' $ f P.⋆ α .snd c .fst q)
            ≡⟨ α .fst .snd c' c f (α .snd c .fst q) ⟩
          f Q.⋆ (α .fst .fst c $ α .snd c .fst q)
            ≡⟨ Q.⟨ refl ⟩⋆⟨ α .snd c .snd .fst q ⟩ ⟩
          f Q.⋆ q
            ∎ ))
    where
      Pc≡Qc : ∀ c → P.p[ c ] ≡ Q.p[ c ]
      Pc≡Qc c i = ⟨ CatIsoToPath isUnivalentSET' (PshIso→SETIso α c) i ⟩

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}where
  idPshIso : PshIso P P
  idPshIso .fst = idPshHom
  idPshIso .snd x = IsoToIsIso idIso

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'}{R : Presheaf C ℓS''} where
  seqIsPshIso : ∀ {α : PshHom P Q}{β : PshHom Q R}
    → isPshIso {P = P}{Q = Q} α
    → isPshIso {P = Q}{Q = R} β
    → isPshIso {P = P}{Q = R} (α ⋆PshHom β)
  seqIsPshIso {α}{β} αIsIso βIsIso x = IsoToIsIso $
    compIso (isIsoToIso (αIsIso x)) (isIsoToIso (βIsIso x))

  _⋆PshIso_ : PshIso P Q → PshIso Q R → PshIso P R
  (α ⋆PshIso β) .fst = α .fst ⋆PshHom β .fst
  (α ⋆PshIso β) .snd x =
    IsoToIsIso $
      compIso (isIsoToIso (α .snd x)) (isIsoToIso (β .snd x))

module _ {C : Category ℓ ℓ'}{P Q : Presheaf C ℓS} (path : P ≡ Q) where
  pathToPshIso : PshIso P Q
  pathToPshIso = PshCatIso→PshIso _ _ (pathToIso path)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS} where
  pathToPshIsoRefl : pathToPshIso (refl {x = P}) ≡ idPshIso
  pathToPshIsoRefl = makePshIsoPath $ funExt λ _ → funExt λ _ →
    transportTransport⁻ _ _

module _ {C : Category ℓ ℓ'}{x} where
  open Category
  pathToPshIsoYo :
    ∀ {P : Presheaf C ℓ'}(yx≡P : C [-, x ] ≡ P)
    → pathToPshIso yx≡P .fst ≡ yoRec P (transport (λ i → yx≡P i .F-ob x .fst) $ C .id)
  pathToPshIsoYo =
    J (λ P yx≡P → pathToPshIso yx≡P .fst ≡ yoRec P (transport (λ i → yx≡P i .F-ob x .fst) $ C .id))
      (cong fst pathToPshIsoRefl ∙ (sym $ yoRec≡ (C [-, x ]) $ transportRefl _))

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS) where
  private
    module P = PresheafNotation P
    module C = Category C

  RepresentationPshIso : Type _
  RepresentationPshIso = Σ[ x ∈ _ ] PshIso (C [-, x ]) P

  open UniversalElement
  module _ ((x , α) : RepresentationPshIso) where
    -- this whole thing could be a subst of yoRecIso P x but this
    -- definition has fewer transports
    RepresentationPshIso→UniversalElement : UniversalElement C P
    RepresentationPshIso→UniversalElement .vertex = x
    RepresentationPshIso→UniversalElement .element = α .fst .fst _ C.id
    RepresentationPshIso→UniversalElement .universal Γ = isIsoToIsEquiv
      ( α⁻ Γ
      , subst motive
          (funExt λ f → sym $ funExt⁻ (funExt⁻ (cong fst $ IsoYoRec P x .Iso.rightInv (α .fst)) _) _)
          (α .snd Γ .snd))
      where
        α⁻ = (invPshIso α) .fst .fst
        motive : (C [ Γ , x ] → P.p[ Γ ]) → Type _
        motive intro⁻ = section intro⁻ (α⁻ Γ) × retract intro⁻ (α⁻ Γ)

-- These things only make sense when the presheaf is at the same
-- universe level as the Homs of the category.
module _ (C : Category ℓ ℓ')(P : Presheaf C ℓ') where
  private
    module C = Category C
  -- A version of Representation that depends on Univalence to be useful
  Representsᵁ : ∀ (x : C.ob) → Type _
  Representsᵁ x = C [-, x ] ≡ P

  Representationᵁ : Type _
  Representationᵁ = fiber (C [-,_]) P

  yoPshIso→Representationᵁ : ∀ {v}{e} → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e) → Representsᵁ v
  yoPshIso→Representationᵁ αIsIso = PshIso→Path (C [-, _ ]) P (yoRec P _ , αIsIso)

  PshIso→Representationᵁ : ∀ {v} → PshIso (C [-, v ]) P → Representationᵁ
  PshIso→Representationᵁ α = _ , PshIso→Path (C [-, _ ]) P α

  UniversalElement→Representationᵁ : UniversalElement C P → Representationᵁ
  UniversalElement→Representationᵁ ue = ue.vertex , PshIso→Path (C [-, ue.vertex ]) P
    ( (yoRec P ue.element)
    , λ x → ue.intro , (λ b → ue.β) , λ _ → sym $ ue.η)
    where
      module ue = UniversalElementNotation ue

  Representationᵁ→RepresentationPshIso : Representationᵁ → RepresentationPshIso P
  Representationᵁ→RepresentationPshIso (v , yv≡P) = v , (PshCatIso→PshIso _ _ $ pathToIso yv≡P)

  Representationᵁ→UniversalElement : Representationᵁ → UniversalElement C P
  Representationᵁ→UniversalElement repr =
    RepresentationPshIso→UniversalElement P
    $ Representationᵁ→RepresentationPshIso repr

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS) where
  private
    module P = PresheafNotation P
  isPshIso→isUniversal : ∀ {v}{e} → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e) → isUniversal C P v e
  isPshIso→isUniversal ⋆eltIsIso A = isIsoToIsEquiv (⋆eltIsIso A)

  isUniversal→isPshIso : ∀ {v}{e} → isUniversal C P v e → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e)
  isUniversal→isPshIso eltIsUniversal A = isEquivToIsIso _ (eltIsUniversal A)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS} (ue : UniversalElement C P) where
  private
    module P = PresheafNotation P
    module ue = UniversalElement ue
  UniversalElement→yoRecIsIso : isPshIso (yoRec P ue.element)
  UniversalElement→yoRecIsIso = isUniversal→isPshIso P ue.universal

  yoRecIso : PshIso (C [-, ue.vertex ]) P
  yoRecIso = (yoRec P ue.element) , UniversalElement→yoRecIsIso

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  open Category
  seqIsUniversalPshIso : ∀ {v e} → isUniversal C P v e → (α : PshIso P Q)
    → isUniversal C Q v (α .fst .fst v e)
  seqIsUniversalPshIso {v}{e} isUe α = isPshIso→isUniversal Q
    λ x → (lem x .fst) ,
          subst (motive x)
            (funExt (λ _ → yoRec-natural-elt P Q (α .fst)))
            (lem x .snd)
    where
      lem : isPshIso ((yoRec P _) ⋆PshHom (α .fst))
      lem = seqIsPshIso {α = yoRec P _}{β = α .fst} (isUniversal→isPshIso P isUe) (α .snd)

      module Q = PresheafNotation Q
      motive : ∀ x → (C [ x , v ] → Q.p[ x ]) → Type _
      motive x Nob =
        section Nob (lem _ .fst)
        × retract Nob (lem _ .fst)
  module _ (ue : UniversalElement C P) (α : PshIso P Q) where
    private
      module ue = UniversalElementNotation ue
    open UniversalElement
    _◃PshIso_ : UniversalElement C Q
    _◃PshIso_ .vertex = ue.vertex
    _◃PshIso_ .element = α .fst .fst ue.vertex ue.element
    _◃PshIso_ .universal = seqIsUniversalPshIso ue.universal α
