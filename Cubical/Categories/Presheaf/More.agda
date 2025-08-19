{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Presheaf.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
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

  isSetPsh : ∀ {x} → isSet (p[ x ])
  isSetPsh {x} = (P ⟅ x ⟆) .snd

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
    weak-η = η ∙ cong intro (∘ᴾId C P _)

    extensionality : ∀ {c} → {f f' : C [ c , vertex ]}
                   → (f P.⋆ element) ≡ (f' P.⋆ element)
                   → f ≡ f'
    extensionality = isoFunInjective (equivToIso (_ , (universal _))) _ _

    intro≡ : ∀ {c} → {p : P.p[ c ]}{f : C [ c , vertex ]}
      → p ≡ f P.⋆ element
      → intro p ≡ f
    intro≡ p≡f*elt = intro⟨ p≡f*elt ⟩ ∙ sym η

    intro-natural : ∀ {c' c} → {p : P.p[ c ]}{f : C [ c' , c ]}
                  → f C.⋆ intro p ≡ intro (f P.⋆ p)
    intro-natural = extensionality
      ( (∘ᴾAssoc C P _ _ _
      ∙ cong (action C P _) β)
      ∙ sym β)

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


{- a PshIso is a PshHom whose underlying functions are iso -}
module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} where
  isPshIso : PshHom P Q → Type _
  isPshIso α = ∀ x → isIso (α .fst x)

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

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS') (((α , α-natural) , αIsIso) : PshIso P Q) where
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


module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'}{R : Presheaf C ℓS''} where
  seqPshHom : PshHom P Q → PshHom Q R → PshHom P R
  seqPshHom α β .fst x p = β .fst x (α .fst x p)
  seqPshHom α β .snd x y f p =
    cong (β .fst _) (α .snd x y f p)
    ∙ β .snd x y f (α .fst y p)

  seqIsPshIso : ∀ {α : PshHom P Q}{β : PshHom Q R}
    → isPshIso {P = P}{Q = Q} α
    → isPshIso {P = Q}{Q = R} β
    → isPshIso {P = P}{Q = R} (seqPshHom α β)
  seqIsPshIso {α}{β} αIsIso βIsIso x = IsoToIsIso $
    compIso (isIsoToIso (αIsIso x)) (isIsoToIso (βIsIso x))

  seqPshIso : PshIso P Q → PshIso Q R → PshIso P R
  seqPshIso α β .fst = seqPshHom (α .fst) (β .fst)
  seqPshIso α β .snd x =
    IsoToIsIso $
      compIso (isIsoToIso (α .snd x)) (isIsoToIso (β .snd x))

-- Recursion principle for representables
module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS) where
  private
    module P = PresheafNotation P
    module C = Category C

  RepresentationPshIso : Type _
  RepresentationPshIso = Σ[ x ∈ _ ] PshIso (C [-, x ]) P

  open UniversalElement
  module _ ((x , ((αN-ob , αN-hom) , αIsIso)) : RepresentationPshIso) where
    RepresentationPshIso→UniversalElement : UniversalElement C P
    RepresentationPshIso→UniversalElement .vertex = x
    RepresentationPshIso→UniversalElement .element = αN-ob _ C.id
    RepresentationPshIso→UniversalElement .universal Γ = isIsoToIsEquiv
    -- Yet another proof of the Yoneda lemma
      ( α⁻N-ob _
      , (λ p →
           isoFunInjective (isIsoToIso (α⁻ .snd _)) _ _
             (α⁻N-hom _ _ _ _
             ∙ C.⟨ refl ⟩⋆⟨ αIsIso _ .snd .snd _ ⟩ ∙ C.⋆IdR _))
      , (λ f → α⁻N-hom _ _ _ _ ∙ C.⟨ refl ⟩⋆⟨ αIsIso _ .snd .snd _ ⟩
        ∙ C.⋆IdR _))
      where
        α⁻ = invPshIso _ P (((αN-ob , αN-hom) , αIsIso))
        α⁻N-ob = α⁻ .fst .fst
        α⁻N-hom = α⁻ .fst .snd

  -- Universe-polymorphic Yoneda recursion principle
  yoRec : ∀ {c} → P.p[ c ] → PshHom (C [-, c ]) P
  yoRec p .fst Γ f = f P.⋆ p
  yoRec p .snd Δ Γ γ f = P.⋆Assoc γ f p

  yoRecβ : ∀ {c}{p : P.p[ c ]} → yoRec p .fst _ C.id ≡ p
  yoRecβ = P.⋆IdL _

  yoRecη : ∀ {c}{α : PshHom (C [-, c ]) P}
    → α ≡ yoRec (α .fst _ C.id)
  yoRecη {α = α} = makePshHomPath (funExt λ _ → funExt λ _ →
    cong (α .fst _) (sym $ C.⋆IdR _)
    ∙ α .snd _ _ _ _)

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS)(Q : Presheaf C ℓS')(α : PshHom P Q) where
  private
    module P = PresheafNotation P
    module C = Category C

  yoRec-natural : ∀ {c}{p : P.p[ c ]} → seqPshHom (yoRec P p) α ≡ yoRec Q (α .fst c p)
  yoRec-natural = makePshHomPath (funExt λ Γ → funExt λ f →
    α .snd _ _ _ _)

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'}
  (α : PshHom P Q) where

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

  Representationᵁ→UniversalElement : Representationᵁ → UniversalElement C P
  Representationᵁ→UniversalElement (v , yv≡P) =
    RepresentationPshIso→UniversalElement P
      (v , (PshCatIso→PshIso _ _ (pathToIso yv≡P)))

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS) where
  private
    module P = PresheafNotation P
  isPshIso→isUniversal : ∀ {v}{e} → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e) → isUniversal C P v e
  isPshIso→isUniversal ⋆eltIsIso A = isIsoToIsEquiv (⋆eltIsIso A)

  isUniversal→isPshIso : ∀ {v}{e} → isUniversal C P v e → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e)
  isUniversal→isPshIso eltIsUniversal A = isEquivToIsIso _ (eltIsUniversal A)

module _ {C : Category ℓ ℓ'}(P : Presheaf C ℓS) (ue : UniversalElement C P) where
  private
    module P = PresheafNotation P
    module ue = UniversalElement ue
  UniversalElement→yoRecIsIso : isPshIso (yoRec P ue.element)
  UniversalElement→yoRecIsIso = isUniversal→isPshIso P ue.universal

module _ {C : Category ℓ ℓ'}{P : Presheaf C ℓS}{Q : Presheaf C ℓS'} (α : PshIso P Q) where
  seqIsUniversalPshIso : ∀ {v e} → isUniversal C P v e → isUniversal C Q v (α .fst .fst v e)
  seqIsUniversalPshIso isUe = isPshIso→isUniversal Q
    λ x → (lem x .fst) ,
          ( (λ q → (sym $ α .fst .snd _ _ _ _) ∙ lem x .snd .fst q)
          , λ f → cong (lem x .fst) (sym $ α .fst .snd _ _ _ _) ∙ lem x .snd .snd f)
          -- better definitional behavior than the equivalent
          -- (subst isPshIso (yoRec-natural P Q _) lem)
    where
      lem : isPshIso (seqPshHom (yoRec P _) (α .fst))
      lem = seqIsPshIso {α = yoRec P _}{β = α .fst} (isUniversal→isPshIso P isUe) (α .snd)

  module _ (ue : UniversalElement C P) where
    private
      module ue = UniversalElementNotation ue
    open UniversalElement
    PshIsoUniversalElement : UniversalElement C Q
    PshIsoUniversalElement .vertex = ue.vertex
    PshIsoUniversalElement .element = α .fst .fst ue.vertex ue.element
    PshIsoUniversalElement .universal = seqIsUniversalPshIso ue.universal
