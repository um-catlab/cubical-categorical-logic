{-
  A natural element of an endo-relator R : C o-* C
  is a "section": ∀ c. R c c that is "natural" in c.

  This is a kind of "nullary" homomorphism of relators.
-}
module Cubical.Categories.Profunctor.Homomorphism.NaturalElement where

open import Cubical.Reflection.RecordEquiv
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Relators
open import Cubical.Categories.Profunctor.Relator

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

open Category
module _ {C : Category ℓC ℓC'}
          where
  record NaturalElement (R : C o-[ ℓR ]-* C) : Type (ℓ-max (ℓ-max ℓC ℓC') ℓR)
    where
    field
      -- the data from an element of the end ∫ R
      N-ob : (x : C .ob) → R [ x , x ]R
      -- the data from a homomorphism Hom -o R
      N-hom : ∀ x y (f : C [ x , y ]) → R [ x , y ]R
      -- N-ob comes from the end
      N-nat : ∀ x y (f : C [ x , y ])
            → (f ⋆l⟨ R ⟩ N-ob y) ≡ (N-ob x ⋆r⟨ R ⟩ f)
      -- N-hom is determined by N-ob
      N-ob-determines-N-hom : ∀ x y (f : C [ x , y ])
        → N-hom x y f ≡ f ⋆l⟨ R ⟩ N-ob y
    N-hom-natL : ∀ x' x y (g : C [ x' , x ])(f : C [ x , y ])
      → N-hom _ _ (g ⋆⟨ C ⟩ f) ≡ g ⋆l⟨ R ⟩ (N-hom _ _ f)
    N-hom-natL x' x y g f =
      N-ob-determines-N-hom _ _ _
      ∙ profAssocL R _ _ _
      ∙ cong (relSeqL' R g) (sym (N-ob-determines-N-hom _ _ _))

    N-hom-natR : ∀ x y y' (f : C [ x , y ])(h : C [ y , y' ])
      → N-hom _ _ (f ⋆⟨ C ⟩ h) ≡ N-hom _ _ f ⋆r⟨ R ⟩ h
    N-hom-natR x y y' f h =
      N-ob-determines-N-hom _ _ _
      ∙ profAssocL R _ _ _
      ∙ cong (relSeqL' R f) (N-nat _ _ _)
      ∙ profAssocLR R _ _ _
      ∙ cong₂ (relSeqR' R) (sym (N-ob-determines-N-hom _ _ _)) refl

    N-hom-determines-N-ob : ∀ x → N-ob x ≡ N-hom _ _ (C .id)
    N-hom-determines-N-ob x = sym (relSeqLId R _)
      ∙ sym (N-ob-determines-N-hom _ _ _)

  -- the end is enough
  mkNaturalElementN-ob : (R : C o-[ ℓR ]-* C)
    → (N-ob : ∀ x → R [ x , x ]R)
    → (∀ x y (f : C [ x , y ]) → (f ⋆l⟨ R ⟩ N-ob y) ≡ (N-ob x ⋆r⟨ R ⟩ f))
    → NaturalElement R
  mkNaturalElementN-ob R N-ob N-nat .NaturalElement.N-ob = N-ob
  mkNaturalElementN-ob R N-ob N-nat .NaturalElement.N-hom x y f =
    f ⋆l⟨ R ⟩ N-ob y
  mkNaturalElementN-ob R N-ob N-nat .NaturalElement.N-nat = N-nat
  mkNaturalElementN-ob R N-ob N-nat .NaturalElement.N-ob-determines-N-hom
    x y f = refl

  mkNaturalElementN-hom : (R : C o-[ ℓR ]-* C)
    → (N-hom : ∀ x y (f : C [ x , y ]) → R [ x , y ]R)
    → (∀ x' x y (g : C [ x' , x ])(f : C [ x , y ])
      → N-hom _ _ (g ⋆⟨ C ⟩ f) ≡ g ⋆l⟨ R ⟩ (N-hom _ _ f))
    → (∀ x y y' (f : C [ x , y ])(h : C [ y , y' ])
      → N-hom _ _ (f ⋆⟨ C ⟩ h) ≡ N-hom _ _ f ⋆r⟨ R ⟩ h)
    → NaturalElement R
  mkNaturalElementN-hom R N-hom N-hom-natL N-hom-natR .NaturalElement.N-ob x =
    N-hom x x (C .id)
  mkNaturalElementN-hom R N-hom N-hom-natL N-hom-natR .NaturalElement.N-hom =
    N-hom
  mkNaturalElementN-hom R N-hom N-hom-natL N-hom-natR .NaturalElement.N-nat
    x y f = sym (N-hom-natL _ _ _ _ _)
    ∙ cong (N-hom x y) (C .⋆IdR f ∙ sym (C .⋆IdL f))
    ∙ N-hom-natR _ _ _ _ _
  mkNaturalElementN-hom R N-hom N-hom-natL N-hom-natR
    .NaturalElement.N-ob-determines-N-hom x y f =
    cong (N-hom x y) (sym (C .⋆IdR f)) ∙ N-hom-natL _ _ _ _ _
  open NaturalElement
  private
    unquoteDecl NatEltIsoΣ = declareRecordIsoΣ NatEltIsoΣ (quote NaturalElement)
  isSetNaturalElement : ∀ {R : C o-[ ℓR ]-* C} → isSet (NaturalElement R)
  isSetNaturalElement {R = R} = isOfHLevelRetractFromIso 2 NatEltIsoΣ (
    isSetΣ (isSetΠ λ x → isSetHet R x x) (λ _ →
    isSetΣ (isSetΠ3 (λ _ _ _ → isSetHet R _ _)) (λ _ →
    isSetΣ (isSetΠ3 (λ _ _ _ → isProp→isSet (isSetHet R _ _ _ _))) (λ _ →
    isSetΠ3 λ _ _ _ → isProp→isSet (isSetHet R _ _ _ _)))))

  NaturalElement≡N-ob : ∀ {R : C o-[ ℓR ]-* C}
    {α β : NaturalElement R}
    → α .N-ob ≡ β .N-ob
    → α ≡ β
  NaturalElement≡N-ob {R = R}{α}{β} α-Nob≡βN-ob = isoFunInjective NatEltIsoΣ _ _
    (ΣPathP (α-Nob≡βN-ob ,
    (ΣPathPProp (λ _ → isProp× (isPropΠ3 (λ _ _ _ → isSetHet R _ _ _ _))
                               (isPropΠ3 λ _ _ _ → isSetHet R _ _ _ _))
    (funExt (λ x → funExt λ y → funExt λ f →
      α .N-ob-determines-N-hom _ _ _
      ∙ cong (relSeqL' R f) (funExt⁻ α-Nob≡βN-ob _)
      ∙ sym (β .N-ob-determines-N-hom _ _ _))))))

  NaturalElement≡N-hom : ∀ {R : C o-[ ℓR ]-* C}
    {α β : NaturalElement R}
    → α .N-hom ≡ β .N-hom
    → α ≡ β
  NaturalElement≡N-hom {R = R}{α}{β} αN-hom≡βN-hom =
    NaturalElement≡N-ob (funExt (λ x →
    N-hom-determines-N-ob α _
    ∙ funExt⁻ (funExt⁻ (funExt⁻ αN-hom≡βN-hom x) x) (C .id)
    ∙ sym (N-hom-determines-N-ob β _)))

  open Functor
  NATURAL-ELEMENTS : Functor (RELATOR C C ℓR) (SET _)
  NATURAL-ELEMENTS .F-ob R = (NaturalElement R) , isSetNaturalElement
  NATURAL-ELEMENTS .F-hom ϕ α .N-ob x = ((ϕ ⟦ x ⟧) ⟦ x ⟧) (α .N-ob x)
  NATURAL-ELEMENTS .F-hom ϕ α .N-hom x y f = ((ϕ ⟦ x ⟧) ⟦ y ⟧) (α .N-hom x y f)
  NATURAL-ELEMENTS .F-hom ϕ α .N-nat x y f = sym (relHomoL ϕ _ _)
    ∙ cong (relHomoAct ϕ) (α .N-nat _ _ _)
    ∙ relHomoR ϕ _ _
  NATURAL-ELEMENTS .F-hom ϕ α .N-ob-determines-N-hom x y f = cong (relHomoAct ϕ)
    (α .N-ob-determines-N-hom _ _ _)
    ∙ relHomoL ϕ _ _
  NATURAL-ELEMENTS .F-id = funExt λ α → NaturalElement≡N-ob (funExt λ x → refl)
  NATURAL-ELEMENTS .F-seq ϕ ψ = funExt (λ α → NaturalElement≡N-ob (funExt λ x →
    refl))
