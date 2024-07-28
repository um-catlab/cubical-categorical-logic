{-# OPTIONS --safe --lossy-unification #-}
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
open import Cubical.Categories.Constructions.Relators
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Profunctor.General
open import Cubical.Categories.Profunctor.Relator
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Profunctor.Homomorphism.NaturalElement
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

HomP : (C : Category ℓC ℓC') → Profunctor C C ℓC'
HomP C .F-ob x = C [-, x ]
HomP C .F-hom f .NatTrans.N-ob w g = (C Category.⋆ g) f
HomP C .F-hom f .NatTrans.N-hom h = funExt (λ g → C .⋆Assoc _ _ _)
HomP C .F-id = makeNatTransPath (funExt (λ x → funExt λ g → C .⋆IdR g))
HomP C .F-seq f g = makeNatTransPath (funExt λ _ → funExt λ h →
  sym (C .⋆Assoc _ _ _))

HomR : ∀ (C : Category ℓC ℓC') → C o-[ ℓC' ]-* C
HomR C = Profunctor→Relatoro* (HomP C)

module _ {C : Category ℓC ℓC'} where
  open NaturalElement
  IdHom : NaturalElement (HomR C)
  IdHom .N-ob x = C .id
  IdHom .N-hom x y f = f
  IdHom .N-nat x y f = C .⋆IdR f ∙ sym (C .⋆IdL f)
  IdHom .N-ob-determines-N-hom x y f = sym (C .⋆IdR f)

  module _ {R : C o-[ ℓC' ]-* C} (α : NaturalElement R) where
    rec : RELATOR C C ℓC' [ HomR C , R ]
    rec .N-ob x .N-ob y f = α .N-hom x y f
    rec .N-ob x .N-hom {x'}{y} h = funExt λ f → N-hom-natR α _ _ _ f h
    rec .N-hom g =
      makeNatTransPath (funExt (λ x' → funExt (N-hom-natL α _ _ _ g)))

    recβ : (NATURAL-ELEMENTS ⟪ rec ⟫) IdHom ≡ α
    recβ = NaturalElement≡N-hom refl

  module _ {R : C o-[ ℓC' ]-* C} where
    recη : (ϕ : RELATOR C C ℓC' [ HomR C , R ])
      → rec ((NATURAL-ELEMENTS ⟪ ϕ ⟫) IdHom) ≡ ϕ
    recη ϕ = makeNatTransPath (funExt λ x → makeNatTransPath refl)

  UniversalNaturalElement
    : UniversalElement ((RELATOR C C ℓC') ^op) NATURAL-ELEMENTS
  UniversalNaturalElement .vertex = HomR C
  UniversalNaturalElement .element = IdHom
  UniversalNaturalElement .universal P =
    isoToIsEquiv (iso _ rec recβ recη)

-- -- TODO: port this to new formulation
-- -- NatElt→NatTrans :
-- --   {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
-- --   {F : Functor C D}{G : Functor C D}
-- --   → NatElt (Hom D ∘Flr (F ^opF , G)) → NatTrans F G
-- -- NatElt→NatTrans ε .NatTrans.N-ob = ε .NatElt.N-ob
-- -- NatElt→NatTrans ε .NatTrans.N-hom = NatElt.N-LR-agree ε
