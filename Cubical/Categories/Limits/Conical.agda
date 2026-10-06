{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Limits.Conical where

open import Cubical.Foundations.Prelude

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions.Reindex

private
  variable
    ℓj ℓj' ℓc ℓc' ℓd ℓd' : Level

open Category
open Functor
open NatTrans

Cones : {C : Category ℓc ℓc'} {J : Category ℓj ℓj'} → Functor J C → Presheaf C _
Cones D = RightAdjointProf ΔCone ⟅ D ⟆

module _ {C : Category ℓc ℓc'} {J : Category ℓj ℓj'} where
  module _ {D : Category ℓd ℓd'} (F : Functor C D) (K : Functor J C) where
    preservesCones : PshHet F (Cones K) (Cones (F ∘F K))
    preservesCones .PshHom.N-ob v π .N-ob j = F ⟪ π ⟦ j ⟧ ⟫
    preservesCones .PshHom.N-ob v π .N-hom k =
      D .⋆IdL _
      ∙ cong (F ⟪_⟫) (sym (C .⋆IdL _) ∙ π .N-hom k)
      ∙ F .F-seq _ _
    preservesCones .PshHom.N-hom _ _ γ π =
      makeNatTransPath (funExt λ j → F .F-seq γ (π ⟦ j ⟧))

    preservesLimit : limit K → Type _
    preservesLimit = preservesUniversalElement preservesCones

module LimitNotation {C : Category ℓc ℓc'} {J : Category ℓj ℓj'} {D : Functor J C}
  (lm : limit D) where
  open UniversalElementNotation lm public

  lim : C .ob
  lim = vertex

  π : NatTrans (ΔCone ⟅ lim ⟆) D
  π = element
