{-# OPTIONS --safe #-}
module Cubical.Categories.Profunctor.Hom where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.HomFunctor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Instances.Functors.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Profunctor.NaturalElement
open import Cubical.Categories.Profunctor.Homomorphism.Unary
open import Cubical.Categories.Bifunctor.Redundant as Bif

private
  variable
    ℓB ℓB' ℓC ℓC' ℓD ℓD' ℓS ℓR ℓQ : Level

open Category
open Functor
open NaturalElement
open NatTrans
open UniversalElement

Hom : (C : Category ℓC ℓC') → Profunctor C C ℓC'
Hom C .F-ob x = C [-, x ]
Hom C .F-hom f .NatTrans.N-ob w g = (C Category.⋆ g) f
Hom C .F-hom f .NatTrans.N-hom h = funExt (λ g → C .⋆Assoc _ _ _)
Hom C .F-id = makeNatTransPath (funExt (λ x → funExt λ g → C .⋆IdR g))
Hom C .F-seq f g = makeNatTransPath (funExt λ _ → funExt λ h →
  sym (C .⋆Assoc _ _ _))

module _ {C : Category ℓC ℓC'} where
  open NaturalElement
  IdHom : NaturalElement (Hom C)
  IdHom .N-ob = λ x → Category.id C
  IdHom .N-nat x y f = C .⋆IdR f ∙ sym (C .⋆IdL f)

  module _ {P : Profunctor C C ℓC'} (α : NaturalElement P) where
    rec : PROFUNCTOR C C ℓC' [ Hom C , P ]
    rec .N-ob x .N-ob y f = f ⋆l⟨ P ⟩ α .N-ob x
    rec .N-ob x .N-hom f = funExt λ g → profAssocL P f g (α .N-ob x)
    rec .N-hom f = makeNatTransPath (funExt λ z → funExt λ g →
      profAssocL P g f (α .N-ob _)
      ∙ cong (profSeqL' P g) (α .N-nat _ _ f)
      ∙ profAssocLR P g (α .N-ob _) f)

    recβ : (NATURAL-ELEMENTS ⟪ rec ⟫) IdHom ≡ α
    recβ = NaturalElement≡ (funExt λ x → funExt⁻ ((P ⟅ _ ⟆) .F-id) _)

  module _ {P : Profunctor C C ℓC'} where
    recη : (ϕ : NatTrans (Hom C) P)
      → rec ((NATURAL-ELEMENTS ⟪ ϕ ⟫) IdHom) ≡ ϕ
    recη ϕ = makeNatTransPath (funExt λ x → makeNatTransPath (funExt λ y →
      funExt λ f →
      sym (ϕ-homoL ϕ f _)
      ∙ cong (ϕ .N-ob _ .N-ob _) (C .⋆IdR f)))

  UniversalNaturalElement : UniversalElement (PROFUNCTOR C C ℓC' ^op)
    NATURAL-ELEMENTS
  UniversalNaturalElement .vertex = Hom C
  UniversalNaturalElement .element = IdHom
  UniversalNaturalElement .universal P =
    isoToIsEquiv (iso _ rec recβ recη)

-- TODO: port this to new formulation
-- NatElt→NatTrans :
--   {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
--   {F : Functor C D}{G : Functor C D}
--   → NatElt (Hom D ∘Flr (F ^opF , G)) → NatTrans F G
-- NatElt→NatTrans ε .NatTrans.N-ob = ε .NatElt.N-ob
-- NatElt→NatTrans ε .NatTrans.N-hom = NatElt.N-LR-agree ε
