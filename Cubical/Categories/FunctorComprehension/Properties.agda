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
open NatIso
open UniversalElement
open UniversalElementNotation
open PshHom

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
    module uesC {c} = UniversalElementNotation (uesC c)
    module uesD {d} = UniversalElementNotation (uesD d)

  preservesProvidedUniversalElementsNatTrans :
    NatTrans
      (F ∘F FunctorComprehension PC uesC)
      (FunctorComprehension PD uesD ∘F F)
  preservesProvidedUniversalElementsNatTrans .N-ob c =
    uesD.intro (α c .N-ob _ (uesC c .element))
  preservesProvidedUniversalElementsNatTrans .N-hom f =
    uesD.intro-natural
    ∙ uesD.intro⟨
      PD.⟨ {!pres-ues!} ⟩⋆⟨ refl ⟩
      ∙ {!!}
      ⟩
    ∙ sym uesD.intro-natural

  -- preservesProvidedUniversalElementsNatIso :
  --   NatIso
  --     (F ∘F FunctorComprehension PC uesC)
  --     (FunctorComprehension PD uesD ∘F F)
  -- preservesProvidedUniversalElementsNatIso .trans =
  --   preservesProvidedUniversalElementsNatTrans
  -- preservesProvidedUniversalElementsNatIso .nIso c =
  --   isiso
  --     (the-is-iso .fst (uesD (F-ob F c) .element))
  --     (intro-natural (uesD _)
  --     ∙ intro≡ (uesD _)
  --         (the-is-iso .snd .fst (uesD (F-ob F c) .element)
  --          ∙ (sym $ PD.⋆IdL _)))
  --      {!!}
  --   where
  --   the-is-iso : Iso.isIso _
  --   the-is-iso = isEquivToIsIso _ (pres-ues c (uesD (F-ob F c) .vertex))
