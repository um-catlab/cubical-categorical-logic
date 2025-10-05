module Cubical.Categories.Presheaf.Representable.More where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

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

open import Cubical.Categories.LocallySmall

private
  variable
    ℓc ℓc' ℓd ℓd' ℓp ℓq ℓr : Level

open Category
open Functor
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

    intro≡ : ∀ {c} → {p : P.p[ c ]}{f : C [ c , vertex ]}
      → p ≡ f P.⋆ element
      → intro p ≡ f
    intro≡ = isoInv≡ (universalIso _)

    intro-natural : ∀ {c' c} → {p : P.p[ c ]}{f : C [ c' , c ]}
                  → f C.⋆ intro p ≡ intro (f P.⋆ p)
    intro-natural = sym $ intro≡ $ P.⟨⟩⋆⟨ sym $ β ⟩ ∙ (sym $ P.⋆Assoc _ _ _)

  ⋆element-isPshIso : isPshIso (yoRec P element)
  ⋆element-isPshIso x = IsoToIsIso (universalIso _)

  asPshIso : PshCatIso (C [-, vertex ]) P
  asPshIso = PshIso→PshCatIso (pshiso (yoRec P element) ⋆element-isPshIso)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp) where
  private
    module P = PresheafNotation P
    module C = Category C
    module PshC = LocallySmallCategoryᴰNotation (PRESHEAF C)

  subst-isUniversal : ∀ {v e e'} → e ≡ e' → isUniversal C P v e → isUniversal C P v e'
  subst-isUniversal {v} e≡e' eIsUniversal Γ = isIsoToIsEquiv (intro , subst motive e≡e'
    (isEquivToIsIso _ (eIsUniversal Γ) .snd))
    where
    ue : UniversalElement C P
    ue = record { vertex = _ ; element = _ ; universal = eIsUniversal }
    open UniversalElementNotation ue
    motive : P.p[ v ] → Type _
    motive e = (section (λ (f : C [ Γ , v ]) → f P.⋆ e) intro) × (retract (λ (f : C [ Γ , v ]) → f P.⋆ e) intro)

  subst-UniversalElement :
    ∀ (ue : UniversalElement C P)
    → ∀ {e} → (ue .UniversalElement.element ≡ e)
    → UniversalElement C P
  subst-UniversalElement ue ue≡e = record { vertex = _ ; element = _
    ; universal = subst-isUniversal ue≡e (ue .UniversalElement.universal) }

  open UniversalElement
  PshIso→UniversalElement : ∀ {v} → PshCatIso (C [-, v ]) P → UniversalElement C P
  PshIso→UniversalElement {v} α .vertex = v
  PshIso→UniversalElement {v} α .element = α .CatIsoᴰ.funᴰ .N-ob v C.id
  PshIso→UniversalElement {v} α .universal Γ = isIsoToIsEquiv
      (α .CatIsoᴰ.invᴰ .N-ob Γ
      , subst motive
          (sym $ funExt⁻ (cong N-ob $ IsoYoRec P v .Iso.rightInv (α .CatIsoᴰ.funᴰ)) Γ)
          ( funExt₂⁻ (cong N-ob $ PshC.≡out (α .CatIsoᴰ.secᴰ)) Γ
          , funExt₂⁻ (cong N-ob $ PshC.≡out (α .CatIsoᴰ.retᴰ)) Γ))
      where
        motive : (C [ Γ , v ] → P.p[ Γ ]) → Type _
        motive intro⁻ = section intro⁻ (α .CatIsoᴰ.invᴰ .N-ob Γ) × retract intro⁻ (α .CatIsoᴰ.invᴰ .N-ob Γ)

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

  yoRecIso : PshCatIso (C [-, ue.vertex ]) P
  yoRecIso = PshIso→PshCatIso (pshiso (yoRec P ue.element) UniversalElement→yoRecIsIso)

module _ {C : Category ℓc ℓc'}(P : Presheaf C ℓp) where
  private
    module P = PresheafNotation P
    module PshC = LocallySmallCategoryᴰNotation (PRESHEAF C)
  open UniversalElementNotation
  IsoYoRecIso : ∀ v → Iso (Σ[ e ∈ P.p[ v ] ] isUniversal C P v e)
                          (PshCatIso (C [-, v ]) P)
  IsoYoRecIso v .Iso.fun (e , eIsUniversal) = yoRecIso (record { vertex = v ; element = e ; universal = eIsUniversal })
  IsoYoRecIso v .Iso.inv α = _ , PshIso→UniversalElement P α .universal
  IsoYoRecIso v .Iso.rightInv α = CatIsoᴰPathP (PRESHEAF C) (ΣPathP (refl , (sym $ yoRecη P)))
  IsoYoRecIso v .Iso.leftInv f = ΣPathPProp (isPropIsUniversal C P v) (yoRecβ P)

module _ {C : Category ℓc ℓc'}{P : Presheaf C ℓp}{Q : Presheaf C ℓq} where
  private
    module P = PresheafNotation P
    module PshC = LocallySmallCategoryᴰNotation (PRESHEAF C)

  open UniversalElement
  _◁PshIso_ : (ue : UniversalElement C P) (α : PshCatIso P Q) → UniversalElement C Q
  ue ◁PshIso α = subst-UniversalElement Q
    (PshIso→UniversalElement Q $ reindPshCatIso (yoRecIso ue PshC.ISOCᴰ.⋆ᴰ α))
    (cong (α .CatIsoᴰ.funᴰ .N-ob _) $ P.⋆IdL _)
