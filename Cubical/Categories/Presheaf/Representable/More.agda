module Cubical.Categories.Presheaf.Representable.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation.Base
open import Cubical.Reflection.RecordEquiv

open import Cubical.Categories.Category renaming (isIso to isIsoC)
open import Cubical.Categories.Constructions.Elements
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Properties renaming (PshIso to PshIsoLift)
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Yoneda

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr : Level

open PshHom
open PshIso

module _ {C : Category ℓc ℓc'} (P : Presheaf C ℓp) where
  private
    module C = Category C
    module P = PresheafNotation P
  -- Universe-polymorphic Yoneda recursion principle
  yoRec : ∀ {c} → P.p[ c ] → PshHom (C [-, c ]) P
  yoRec p .N-ob Γ f = f P.⋆ p
  yoRec p .N-hom Δ Γ γ f = P.⋆Assoc γ f p

  yoRecβ : ∀ {c}{p : P.p[ c ]} → yoRec p .N-ob _ C.id ≡ p
  yoRecβ = P.⋆IdL _

  yoRecη-elt : ∀ {c}(α : PshHom (C [-, c ]) P){Γ}{f : C [ Γ , c ]}
    → α .N-ob Γ f ≡ yoRec (α .N-ob _ C.id) .N-ob Γ f
  yoRecη-elt α =
    cong (α .N-ob _) (sym $ C.⋆IdR _)
    ∙ α .N-hom _ _ _ _

  yoRecη : ∀ {c}{α : PshHom (C [-, c ]) P}
    → α ≡ yoRec (α .N-ob _ C.id)
  yoRecη {α = α} = makePshHomPath (funExt (λ _ → funExt (λ _ → yoRecη-elt α)))

  IsoYoRec : ∀ c → Iso P.p[ c ] (PshHom (C [-, c ]) P)
  IsoYoRec c =
    iso yoRec (λ α → α .N-ob c C.id) (λ _ → sym $ yoRecη) (λ _ → yoRecβ)

  yoRec≡ : ∀ {c} {p : P.p[ c ]}{α}
    → p ≡ α .N-ob _ C.id
    → yoRec p ≡ α
  yoRec≡ = isoFun≡ (IsoYoRec _)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp)(Q : Presheaf C ℓq)(α : PshHom P Q) where
  private
    module P = PresheafNotation P
    module C = Category C

  yoRec-natural-elt : ∀ {Γ c}{f : C [ Γ , c ]}{p : P.p[ c ]}
    → α .N-ob _ (yoRec P p .N-ob _ f) ≡ yoRec Q (α .N-ob c p) .N-ob Γ f
  yoRec-natural-elt = α .N-hom _ _ _ _

  yoRec-natural : ∀ {c}{p : P.p[ c ]} → (yoRec P p) ⋆PshHom α ≡ yoRec Q (α .N-ob c p)
  yoRec-natural = makePshHomPath $ funExt λ _ → funExt λ _ → yoRec-natural-elt

module UniversalElementNotation {ℓo}{ℓh}
       {C : Category ℓo ℓh} {ℓp} {P : Presheaf C ℓp}
       (ue : UniversalElement C P)
       where
  open Category
  open UniversalElement ue public
  REPR : Representation C P
  REPR = universalElementToRepresentation C P ue

  unIntroNT : NatTrans (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
                       (LiftF {ℓ' = ℓh} ∘F P)
  unIntroNT = REPR .snd .NatIso.trans

  introNI : NatIso (LiftF {ℓ' = ℓh} ∘F P) (LiftF {ℓ' = ℓp} ∘F (C [-, vertex ]))
  introNI = symNatIso (REPR .snd)

  universalIso : ∀ (c : C .ob) → Iso (C [ c , vertex ]) ⟨ P ⟅ c ⟆ ⟩
  universalIso c = equivToIso (_ , universal c)

  private
    module P = PresheafNotation P
    module C = Category C

  intro : ∀ {c} → P.p[ c ] → C [ c , vertex ]
  intro = universalIso _ .Iso.inv

  intro⟨_⟩ : ∀ {c} → {f g : P.p[ c ]} → f ≡ g → intro f ≡ intro g
  intro⟨ p ⟩ = cong intro p

  opaque
    β : ∀ {c} → {p : P.p[ c ]} → (intro p P.⋆ element) ≡ p
    β = universalIso _ .Iso.rightInv _

    η : ∀ {c} → {f : C [ c , vertex ]} → f ≡ intro (f P.⋆ element)
    η {f = f} = sym (universalIso _ .Iso.leftInv _)

    weak-η : C .id ≡ intro element
    weak-η = η ∙ intro⟨ P.⋆IdL _ ⟩

    extensionality : ∀ {c} → {f f' : C [ c , vertex ]}
                   → (f P.⋆ element) ≡ (f' P.⋆ element)
                   → f ≡ f'
    extensionality = isoFunInjective (universalIso _) _ _

    -- this is the best one
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
  asPshIso .trans = yoRec P element
  asPshIso .nIso =  ⋆element-isPshIso

open Functor
module _ {C : Category ℓc ℓc'}{x} where
  open Category
  pathToPshIsoYo :
    ∀ {P : Presheaf C ℓc'}(yx≡P : C [-, x ] ≡ P)
    → pathToPshIso yx≡P .trans ≡ yoRec P (transport (λ i → yx≡P i .F-ob x .fst) $ C .id)
  pathToPshIsoYo =
    J (λ P yx≡P → pathToPshIso yx≡P .trans ≡ yoRec P (transport (λ i → yx≡P i .F-ob x .fst) $ C .id))
      (cong trans pathToPshIsoRefl ∙ (sym $ yoRec≡ (C [-, x ]) $ transportRefl _))

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp) where
  private
    module P = PresheafNotation P
    module C = Category C

  RepresentationPshIso : Type _
  RepresentationPshIso = Σ[ x ∈ C.ob ] PshIso (C [-, x ]) P

  open UniversalElement
  module _ ((x , α) : RepresentationPshIso) where
    -- this whole thing could be a subst of yoRecIso P x but this
    -- definition has fewer transports
    RepresentationPshIso→UniversalElement : UniversalElement C P
    RepresentationPshIso→UniversalElement .vertex = x
    RepresentationPshIso→UniversalElement .element =
      α .trans .N-ob _ C.id
    RepresentationPshIso→UniversalElement .universal Γ = isIsoToIsEquiv
      ( α⁻ Γ
      , subst motive
          (funExt λ f → sym $ funExt⁻ (funExt⁻ (cong N-ob $ IsoYoRec P x .Iso.rightInv (α .trans)) _) _)
          (α .nIso Γ .snd))
      where
        α⁻ = (invPshIso α) .trans .N-ob
        motive : (C [ Γ , x ] → P.p[ Γ ]) → Type _
        motive intro⁻ = section intro⁻ (α⁻ Γ) × retract intro⁻ (α⁻ Γ)

-- These things only make sense when the presheaf is at the same
-- universe level as the Homs of the category.
module _ (C : Category ℓc ℓc')(P : Presheaf C ℓc') where
  private
    module C = Category C
  -- A version of Representation that depends on Univalence to be useful
  Representsᵁ : ∀ (x : C.ob) → Type _
  Representsᵁ x = C [-, x ] ≡ P

  Representationᵁ : Type _
  Representationᵁ = fiber (C [-,_]) P

  yoPshIso→Representationᵁ : ∀ {v}{e} → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e) → Representsᵁ v
  yoPshIso→Representationᵁ αIsIso =
    PshIso→Path (C [-, _ ]) P (record { trans = yoRec P _ ; nIso = αIsIso })

  PshIso→Representationᵁ : ∀ {v} → PshIso (C [-, v ]) P → Representationᵁ
  PshIso→Representationᵁ α = _ , PshIso→Path (C [-, _ ]) P α

  UniversalElement→Representationᵁ : UniversalElement C P → Representationᵁ
  UniversalElement→Representationᵁ ue = ue.vertex , PshIso→Path (C [-, ue.vertex ]) P
    (record { trans = yoRec P ue.element
            ; nIso = λ x → ue.intro , (λ b → ue.β) , λ _ → sym $ ue.η })
    where
      module ue = UniversalElementNotation ue

  Representationᵁ→RepresentationPshIso : Representationᵁ → RepresentationPshIso P
  Representationᵁ→RepresentationPshIso (v , yv≡P) = v , (PshCatIso→PshIso _ _ $ pathToIso yv≡P)

  Representationᵁ→UniversalElement : Representationᵁ → UniversalElement C P
  Representationᵁ→UniversalElement repr =
    RepresentationPshIso→UniversalElement P
    $ Representationᵁ→RepresentationPshIso repr

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp) where
  private
    module P = PresheafNotation P
  isPshIso→isUniversal : ∀ {v}{e} → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e) → isUniversal C P v e
  isPshIso→isUniversal ⋆eltIsIso A = isIsoToIsEquiv (⋆eltIsIso A)

  isUniversal→isPshIso : ∀ {v}{e} → isUniversal C P v e → isPshIso {P = C [-, v ]}{Q = P} (yoRec P e)
  isUniversal→isPshIso eltIsUniversal A = isEquivToIsIso _ (eltIsUniversal A)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp} (ue : UniversalElement C P) where
  private
    module P = PresheafNotation P
    module ue = UniversalElement ue
  UniversalElement→yoRecIsIso : isPshIso (yoRec P ue.element)
  UniversalElement→yoRecIsIso = isUniversal→isPshIso P ue.universal

  yoRecIso : PshIso (C [-, ue.vertex ]) P
  yoRecIso = record { trans = yoRec P ue.element
                    ; nIso = UniversalElement→yoRecIsIso }

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  open Category
  seqIsUniversalPshIso : ∀ {v e} → isUniversal C P v e → (α : PshIso P Q)
    → isUniversal C Q v (α .trans .N-ob v e)
  seqIsUniversalPshIso {v}{e} isUe α = isPshIso→isUniversal Q
    λ x → (lem x .fst) ,
          subst (motive x)
            (funExt (λ _ → yoRec-natural-elt P Q (α .trans)))
            (lem x .snd)
    where
      lem : isPshIso {C = C} ((yoRec P _) ⋆PshHom (α .trans))
      lem = seqIsPshIso {α = yoRec P _}{β = α .trans} (isUniversal→isPshIso P isUe) (α .nIso)

      module Q = PresheafNotation Q
      motive : ∀ x → (C [ x , v ] → Q.p[ x ]) → Type _
      motive x Nob =
        section Nob (lem _ .fst)
        × retract Nob (lem _ .fst)
  module _ (ue : UniversalElement C P) (α : PshIso P Q) where
    private
      module ue = UniversalElementNotation ue
    open UniversalElement
    _◁PshIso_ : UniversalElement C Q
    _◁PshIso_ .vertex = ue.vertex
    _◁PshIso_ .element = α .trans .N-ob ue.vertex ue.element
    _◁PshIso_ .universal = seqIsUniversalPshIso ue.universal α
