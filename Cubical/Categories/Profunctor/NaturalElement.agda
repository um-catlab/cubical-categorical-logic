{-

  A natural element of a profunctor R : C -|-> C is a "section": ∀
  c. R c c that is "natural" in c, equivalently an element of the end
  ∫ R.

  This is a kind of "nullary" homomorphism of relators. The set of all
  such natural elements is known sometimes in the literature as the
  cotrace of R, and if R = Hom_C this is called the "center" of C.

-}
{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Profunctor.NaturalElement where

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
open import Cubical.Categories.Profunctor.General
import Cubical.Categories.Profunctor.Relator as Relator
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

open Category
module _ {C : Category ℓC ℓC'} where
  --
  record NaturalElement (R : Profunctor C C ℓR)
    : Type (ℓ-max (ℓ-max ℓC ℓC') ℓR) where
    field
      N-ob : (x : C .ob) → R [ x , x ]P
      N-nat : ∀ x y (f : C [ x , y ])
            → (f ⋆l⟨ R ⟩ N-ob y) ≡ (N-ob x ⋆r⟨ R ⟩ f)

  open Functor
  open NaturalElement
  open NatTrans
  unquoteDecl NatEltIsoΣ = declareRecordIsoΣ NatEltIsoΣ (quote NaturalElement)
  isSetNaturalElement : ∀ {R : Profunctor C C ℓR} → isSet (NaturalElement R)
  isSetNaturalElement {R = R} = isOfHLevelRetractFromIso 2 NatEltIsoΣ (isSetΣ
    (isSetΠ λ x → ((R ⟅ x ⟆) ⟅ x ⟆) .snd)
    λ N-ob → isSetΠ (λ x → isSetΠ λ y → isSetΠ λ f →
      isProp→isSet (((R ⟅ y ⟆) ⟅ x ⟆) .snd _ _)))

  NaturalElement≡ : ∀ {R : Profunctor C C ℓR}
    {α β : NaturalElement R}
    → α .N-ob ≡ β .N-ob
    → α ≡ β
  NaturalElement≡ {R = R} α1≡β1 = isoFunInjective NatEltIsoΣ _ _ (ΣPathPProp
    (λ hom → isPropΠ3 λ _ _ _ → isSetHet R _ _ _ _ )
    α1≡β1)

  NATURAL-ELEMENTS : Functor (PROFUNCTOR C C ℓR) (SET _)
  NATURAL-ELEMENTS .F-ob P = NaturalElement P , isSetNaturalElement
  NATURAL-ELEMENTS .F-hom {x = P}{y = Q} ϕ α .N-ob x =
    ((ϕ ⟦ x ⟧) ⟦ x ⟧) (α .N-ob x)
  NATURAL-ELEMENTS .F-hom {x = P}{y = Q} ϕ α .N-nat x y f =
    sym (ϕ-homoL ϕ f _)
    ∙ cong (prof-act ϕ) (α .N-nat _ _ f)
    ∙ ϕ-homoR ϕ _ f
  NATURAL-ELEMENTS .F-id = funExt (λ α → NaturalElement≡ (funExt λ x → refl))
  NATURAL-ELEMENTS .F-seq ϕ ψ =
    funExt (λ α → NaturalElement≡ (funExt λ x → refl))

  module _ (R : Profunctor C C ℓR) where
    open Relator.NatElt
    NaturalElement→NatElt : NaturalElement R
      → Relator.NatElt (Relator.Profunctor→Relatoro* R)
    NaturalElement→NatElt α .N-ob = α .N-ob
    NaturalElement→NatElt α .N-hom× f = f ⋆l⟨ R ⟩ α .N-ob _
    NaturalElement→NatElt α .N-ob-hom×-agree = funExt⁻ (R .F-ob _ .F-id) _
    NaturalElement→NatElt α .N-natL = λ _ → refl
    NaturalElement→NatElt α .N-natR = α .N-nat _ _
