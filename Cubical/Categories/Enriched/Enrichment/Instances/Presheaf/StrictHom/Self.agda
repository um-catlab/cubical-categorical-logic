{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Monoidal.Base
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct using (_×Psh_)
open import Cubical.Categories.Presheaf.Constructions.Lift
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Instances.Presheaf.StrictHom.Self using (self)
open import Cubical.Categories.Monoidal.Enriched using (EnrichedCategory)

-- Self-enrichment of the presheaf category over itself (StrictHom variant),
-- in the new `Enrichment` record form.
module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level)
  where

open PshMon A ℓS

selfEC = self A ℓS

open Cubical.Categories.Enriched.Enrichment.Base 𝓟 𝓟Mon

open Category
open Functor
open PshHomStrict

private
  variable
    P Q : ob 𝓟

  -- 𝟙 = LiftPsh UnitPsh ℓm; supply a UnitPsh-style intro that lands in it.
  𝟙-intro : ∀ {P : Presheaf A ℓm} → PshHomStrict P 𝟙
  𝟙-intro .N-ob _ _ = lift tt
  𝟙-intro .N-hom _ _ _ _ _ _ = refl

  -- Project the second factor out of 𝟙 ×Psh P.
  π₂-from-𝟙 : PshHomStrict (𝟙 ×Psh P) P
  π₂-from-𝟙 = π₂ 𝟙 _

  ⌜_⌝ : PshHomStrict P Q → PshHomStrict 𝟙 (Q ^ P)
  ⌜ f ⌝ = λPshHomStrict _ _ (π₂-from-𝟙 ⋆PshHomStrict f)

  ⌞_⌟ : PshHomStrict 𝟙 (Q ^ P) → PshHomStrict P Q
  ⌞ α ⌟ =
    ×PshIntroStrict (𝟙-intro ⋆PshHomStrict α) idPshHomStrict
      ⋆PshHomStrict appPshHomStrict _ _

  ⇄-agree-iso : Iso (PshHomStrict P Q) (PshHomStrict 𝟙 (Q ^ P))
  ⇄-agree-iso .Iso.fun = ⌜_⌝
  ⇄-agree-iso .Iso.inv = ⌞_⌟
  ⇄-agree-iso .Iso.sec α = makePshHomStrictPath
    (funExt λ c → funExt λ _ → makePshHomStrictPath
      (funExt λ d → funExt λ (f , p) →
        sym (cong (λ x → α .N-ob c _ .N-ob d (x , p)) (sym (A .⋆IdL f))
        ∙ funExt⁻ (funExt⁻ (cong N-ob (α .N-hom d c f _ _ refl)) d) (A .id , p))))
  ⇄-agree-iso .Iso.ret f = makePshHomStrictPath
    (funExt λ c → funExt λ p → cong (λ x → f .N-ob c x) refl)

selfEnrichment : Enrichment
selfEnrichment .Enrichment.VE[_,_] P Q = Q ^ P
selfEnrichment .Enrichment.id = selfEC .EnrichedCategory.id
selfEnrichment .Enrichment.seq P Q R = selfEC .EnrichedCategory.seq P Q R
selfEnrichment .Enrichment.⇄-agree = ⇄-agree-iso
selfEnrichment .Enrichment.⋆IdL P Q = selfEC .EnrichedCategory.⋆IdL P Q
selfEnrichment .Enrichment.⋆IdR P Q = selfEC .EnrichedCategory.⋆IdR P Q
selfEnrichment .Enrichment.⋆Assoc P Q R S = selfEC .EnrichedCategory.⋆Assoc P Q R S
selfEnrichment .Enrichment.⌜id⌝ = makePshHomStrictPath
  (funExt λ c → funExt λ _ →
    makePshHomStrictPath
      (funExt λ d → funExt λ _ → refl))
selfEnrichment .Enrichment.⌜⋆⌝ f g = makePshHomStrictPath
  (funExt λ c → funExt λ _ →
    makePshHomStrictPath
      (funExt λ d → funExt λ (α , p) → refl))
