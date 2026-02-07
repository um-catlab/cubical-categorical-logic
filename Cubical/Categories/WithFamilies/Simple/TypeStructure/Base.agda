module Cubical.Categories.WithFamilies.Simple.TypeStructure.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.WithFamilies.Simple.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level

open UniversalElement
open PshIso

module _ (S : SCwF ℓC ℓC' ℓT ℓT') where
  private
    module S = SCwF S
  Sole : S.Ty → S.C.ob
  Sole A = S.ext.vertex S.term.𝟙 A

  AllTmRepr : ∀ A → UniversalElement S.C (S.Tm A)
  AllTmRepr A .vertex = S.ext.vertex S.term.𝟙 A
  AllTmRepr A .element = S.ext.element S.term.𝟙ue.vertex A .snd
  AllTmRepr A .universal Γ = isIsoToIsEquiv
    ( (λ M → S.ext.intro _ _ (S.term.!t , M))
    , (λ M → PathPΣ (S.ext.β _ _) .snd)
    , λ γ → S.ext.intro≡ _ _ (ΣPathP (S.term.𝟙extensionality , refl)))

  Tm≅Sole : ∀ A → PshIso (S.C [-, Sole A ]) (S.Tm A)
  Tm≅Sole A = yoRecIso (AllTmRepr A)

  TypeSpec : ∀ ℓS → Type (ℓ-max (ℓ-max ℓC ℓC') (ℓ-suc ℓS))
  TypeSpec ℓS = Presheaf S.C ℓS

  -- A type structure is a "code" for a presheaf
  TypeStr : TypeSpec ℓS → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓT) ℓT') ℓS)
  TypeStr P = Σ[ A ∈ S.Ty ] PshIso (S.Tm A) P

  TyStrUE : TypeSpec ℓS → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓT) ℓT') ℓS)
  TyStrUE P =
    Σ[ A ∈ S.Ty ]
    Σ[ e ∈ P.p[ S.ext.vertex S.term.𝟙 A ] ]
    isPshIso {P = S.Tm A}{Q = P}(invPshIso (Tm≅Sole A) .trans ⋆PshHom yoRec P e)
    where module P = PresheafNotation P
  TyStrUE→PshIso : (P : TypeSpec ℓS) (ue : TyStrUE P) → PshIso (S.Tm (ue .fst)) P
  TyStrUE→PshIso P ue .trans = invPshIso (Tm≅Sole _) .trans ⋆PshHom yoRec P (ue .snd .fst)
  TyStrUE→PshIso P ue .nIso = ue .snd .snd
