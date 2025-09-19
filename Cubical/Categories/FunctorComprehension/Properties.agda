module Cubical.Categories.FunctorComprehension.Properties where

open import Cubical.Foundations.Prelude
import Cubical.Foundations.Isomorphism as Iso
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.FunctorComprehension
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Profunctor.General

private
  variable
    ℓC ℓC' ℓD ℓD' ℓE ℓE' ℓS ℓR : Level

open Category
open Functor
open NatTrans
open UniversalElement
open UniversalElementNotation

module _ {C : Category ℓC ℓC'}{D : Category ℓD ℓD'}
         (PC : Profunctor C C ℓC')
         (PD : Profunctor D D ℓD')
         (F : Functor C D)
         (α : ∀ c → PshHet F (PC ⟅ c ⟆) (PD ⟅ F ⟅ c ⟆ ⟆))
         (uesC : UniversalElements PC)
         (uesD : UniversalElements PD)
         (pres-ues : ∀ c → preservesUniversalElement (α c) (uesC c))
         where
  private
    module C = Category C
    module D = Category D
    module PC {c} = PresheafNotation (PC ⟅ c ⟆)
    module PD {d} = PresheafNotation (PD ⟅ d ⟆)

  open UniversalElement

  open PshHom
  preservesProvidedUniversalElementsNatIso :
    NatIso
      (F ∘F FunctorComprehension PC uesC)
      (FunctorComprehension PD uesD ∘F F)
  preservesProvidedUniversalElementsNatIso .NatIso.trans .N-ob c =
    intro (uesD (F ⟅ c ⟆)) (α c .N-ob _ (uesC c .element))
  preservesProvidedUniversalElementsNatIso .NatIso.trans .N-hom f =
    intro-natural (uesD _)
    ∙ {!!}
  preservesProvidedUniversalElementsNatIso .NatIso.nIso c =
    isiso
      (the-is-iso .fst (uesD (F-ob F c) .element))
      (intro-natural (uesD _)
      ∙ intro≡ (uesD _)
          (the-is-iso .snd .fst (uesD (F-ob F c) .element)
           ∙ (sym $ PD.⋆IdL _)))
      ({!!}
      ∙ {!!})
    where
    the-is-iso : Iso.isIso _
    the-is-iso = isEquivToIsIso _ (pres-ues c (uesD (F-ob F c) .vertex))


--   FunctorComprehension : Functor C D
--   FunctorComprehension .F-ob x = ues x .vertex
--   FunctorComprehension .F-hom {x}{y} f =
--     intro (ues y) ((P ⟪ f ⟫) .N-ob _ (ues x .element))
--   FunctorComprehension .F-id {x} =
--     (λ i → intro (ues x) (P .F-id i .N-ob _ (ues x .element)))
--     ∙ (sym $ weak-η (ues x))
--   FunctorComprehension .F-seq {x}{y}{z} f g =
--     ((λ i → intro (ues z) (P .F-seq f g i .N-ob _ (ues x .element))))
--     ∙ (cong (intro (ues z)) $
--       ((λ i → P .F-hom g .N-ob _
--         (β (ues y) {p = P .F-hom f .N-ob _ (ues x .element)} (~ i))))
--       ∙ funExt⁻ (P .F-hom g .N-hom _) _)
--     ∙ (sym $ intro-natural (ues z))

-- module _
--   {C : Category ℓc ℓc'}{D : Category ℓd ℓd'}
--   (F : Functor C D)
--   (P : Profunctor C D ℓs)
--   (ues : UniversalElements P)
--   where
