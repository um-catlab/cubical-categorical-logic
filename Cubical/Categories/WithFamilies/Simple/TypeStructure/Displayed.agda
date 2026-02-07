{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.WithFamilies.Simple.TypeStructure.Displayed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.TypeStructure.Base

private
  variable
    ℓC ℓC' ℓT ℓT' ℓD ℓD' ℓS ℓS' : Level
    ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ' ℓSᴰ ℓSᴰ' : Level

open UniversalElement
open PshIso
open isIsoOver

module _ (S : SCwF ℓC ℓC' ℓT ℓT')(Sᴰ : SCwFᴰ S ℓCᴰ ℓCᴰ' ℓTᴰ ℓTᴰ') where
  private
    module S = SCwF S
    module Sᴰ = SCwFᴰ Sᴰ
  Soleᴰ : {A : S.Ty} (Aᴰ : Sᴰ.Tyᴰ A) → Sᴰ.Cᴰ.ob[ Sole S A ]
  Soleᴰ Aᴰ = Sᴰ.comprehensionᴰ Aᴰ (Sᴰ.termᴰ .fst) .fst

  AllTmReprᴰ : ∀ {A} (Aᴰ : Sᴰ.Tyᴰ A) → UniversalElementᴰ Sᴰ.Cᴰ (S.Tm A) (Sᴰ.Tmᴰ Aᴰ) (AllTmRepr S A)
  AllTmReprᴰ Aᴰ .fst = Sᴰ.comprehensionᴰ Aᴰ (Sᴰ.termᴰ .fst) .fst
  AllTmReprᴰ Aᴰ .snd .fst = Sᴰ.comprehensionᴰ Aᴰ (Sᴰ.termᴰ .fst) .snd .fst .snd
  AllTmReprᴰ Aᴰ .snd .snd Γ Γᴰ .inv M Mᴰ = Sᴰ.comprehensionᴰ.introᴰ (Sᴰ.termᴰ.introᴰ tt , Mᴰ)
  AllTmReprᴰ Aᴰ .snd .snd Γ Γᴰ .rightInv M Mᴰ =
    Sᴰ.Tmᴰ.rectifyOut $
      {!!}
  AllTmReprᴰ Aᴰ .snd .snd Γ Γᴰ .leftInv γ γᴰ = Sᴰ.Cᴰ.rectifyOut $ {!Sᴰ.comprehensionᴰ.ue.intro≡ ?!}

  -- AllTmRepr A .vertex = S.ext.vertex S.term.𝟙 A
  -- AllTmRepr A .element = S.ext.element S.term.𝟙ue.vertex A .snd
  -- AllTmRepr A .universal Γ = isIsoToIsEquiv
  --   ( (λ M → S.ext.intro _ _ (S.term.!t , M))
  --   , (λ M → PathPΣ (S.ext.β _ _) .snd)
  --   , λ γ → S.ext.intro≡ _ _ (ΣPathP (S.term.𝟙extensionality , refl)))

  -- Tm≅Sole : ∀ A → PshIso (S.C [-, Sole A ]) (S.Tm A)
  -- Tm≅Sole A = yoRecIso (AllTmRepr A)

  TypeᴰSpec : ∀ (P : TypeSpec S ℓS) ℓSᴰ → Type _
  TypeᴰSpec P = Presheafᴰ P Sᴰ.Cᴰ

  TypeᴰStrᴰUEᴰ : {P : TypeSpec S ℓS} (Pᴰ : TypeᴰSpec P ℓSᴰ) → TyStrUE S P → Type _
  TypeᴰStrᴰUEᴰ {P = P} Pᴰ (v , e , u) =
    Σ[ vᴰ ∈ Sᴰ.Tyᴰ v ]
    Σ[ eᴰ ∈ Pᴰ.p[ e ][ Sᴰ.comprehensionᴰ.vertexᴰ {Γᴰ = Sᴰ.termᴰ.vertexᴰ}{Aᴰ = vᴰ} ] ]
    isPshIsoᴰ (TyStrUE→PshIso S P (v , e , u))
      (Sᴰ.Tmᴰ vᴰ)
      Pᴰ
      ({!!} ⋆PshHomᴰ yoRecᴰ {P = P} Pᴰ eᴰ)
    where module Pᴰ = PresheafᴰNotation Sᴰ.Cᴰ P Pᴰ
  -- -- A type structure is a "code" for a presheaf
  -- TypeStr : TypeSpec ℓS → Type (ℓ-max (ℓ-max (ℓ-max (ℓ-max ℓC ℓC') ℓT) ℓT') ℓS)
  -- TypeStr P = Σ[ A ∈ S.Ty ] PshIso (S.Tm A) P

  -- TyStrUE : TypeSpec ℓS → Type (ℓ-max (ℓ-max (ℓ-max ℓC ℓT) ℓT') ℓS)
  -- TyStrUE P =
  --   Σ[ A ∈ S.Ty ]
  --   Σ[ e ∈ P.p[ S.ext.vertex S.term.𝟙 A ] ]
  --   isPshIso {P = S.Tm A}{Q = P}(invPshIso (Tm≅Sole A) .trans ⋆PshHom yoRec P e)
  --   where module P = PresheafNotation P
