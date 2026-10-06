{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Categories.Direct.Base
module Cubical.Categories.Direct.Guarded.Presheaf
  {ℓ ℓ' ℓD : Level} {A : Category ℓ ℓ'} {Wo : WFOrder ℓD ℓ'}
  (dir : DirectStr A Wo) where


open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.StrictHom.CartesianClosed
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Monoidal.Guarded
open import Cubical.Categories.Monoidal.NaturalTransformation.Instances.Presheaf.Next dir
  using (▷-lax ; nextNT-monoidal)
open import Cubical.Categories.Direct.StrictDownset dir
open import Cubical.Categories.Enriched.Enrichment.LocallyContractive
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self A ℓ
  using (selfEnrichment)
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Limits A ℓ
  using (Γ×- ; ×-Enr)

open PshHomStrict
open PshMon A ℓ using (𝓟Mon ; ℓm ; 𝟙 ; 𝓟LeftClosed)
open Category A using (id)

private
  name : {X : Presheaf A ℓm} → PshHomStrict (▷Psh X) X
    → PshHomStrict 𝟙 (▷Psh X ⇒PshLargeStrict X)
  name {X} f = λPshHomStrict (▷Psh X) X (π₂ 𝟙 (▷Psh X) ⋆PshHomStrict f)

pshGuardedStr : GuardedStr ▷-lax nextNT-monoidal
pshGuardedStr .GuardedStr.fix {X} f = name f ⋆PshHomStrict löb X
pshGuardedStr .GuardedStr.fix-fix {X} f =
  cong (name f ⋆PshHomStrict_) (löb-fix X) ∙ makePshHomStrictPath refl
pshGuardedStr .GuardedStr.fix-uniq {X} f u p =
  löb-uniq X (name f) u (p ∙ makePshHomStrictPath refl)

pshGuarded : GuardedModel 𝓟Mon
pshGuarded .GuardedModel.▷Lax = ▷-lax
pshGuarded .GuardedModel.next = nextNT-monoidal
pshGuarded .GuardedModel.guardedStr = pshGuardedStr


▷Psh-LC : isLocallyContractive pshGuarded selfEnrichment selfEnrichment ▷
▷Psh-LC = ▷-LC pshGuarded 𝓟LeftClosed

module _ (X : Presheaf A ℓm) where
  private
    E = ▷Psh X ⇒PshLargeStrict X
    module L = Hylo pshGuarded {F = Γ×- E ∘F ▷}
      (LC-postcomp pshGuarded {F = ▷} {H = Γ×- E} ▷Psh-LC (×-Enr E))
      {X = E} {B = X}
      (×PshIntroStrict idPshHomStrict (next E))
      (appPshHomStrict (▷Psh X) X)

    unfold : (u : PshHomStrict E X)
      → ×PshIntroStrict idPshHomStrict (next E)
          ⋆PshHomStrict ((Γ×- E ⟪ ▷ ⟪ u ⟫ ⟫) ⋆PshHomStrict appPshHomStrict (▷Psh X) X)
        ≡ ×PshIntroStrict idPshHomStrict (u ⋆PshHomStrict next X)
          ⋆PshHomStrict appPshHomStrict (▷Psh X) X
    unfold u = makePshHomStrictPath (funExt λ c → funExt λ e →
      cong (λ β → e .N-ob c (id , β)) (makePshHomStrictPath (funExt λ y → funExt λ (g , q) →
        sym (u .N-hom y c g e _ refl))))

  löb' : PshHomStrict (▷Psh X ⇒PshLargeStrict X) X
  löb' = L.hylo

  löb'-fix : löb' ≡ ×PshIntroStrict idPshHomStrict (löb' ⋆PshHomStrict next X)
                      ⋆PshHomStrict appPshHomStrict (▷Psh X) X
  löb'-fix = L.hylo-eq ∙ unfold löb'

  löb'-uniq : (u : PshHomStrict (▷Psh X ⇒PshLargeStrict X) X)
    → u ≡ ×PshIntroStrict idPshHomStrict (u ⋆PshHomStrict next X)
            ⋆PshHomStrict appPshHomStrict (▷Psh X) X
    → u ≡ löb'
  löb'-uniq u p = L.hylo-uniq u (p ∙ sym (unfold u))
