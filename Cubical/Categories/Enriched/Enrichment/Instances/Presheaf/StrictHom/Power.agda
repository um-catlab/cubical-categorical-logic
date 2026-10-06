{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Power
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Limits.Power
open import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self A ℓS

open Functor
open PshHomStrict
open UniversalElement
open PshMon A ℓS using (𝓟 ; ℓm ; _^_)

private
  module A = Category A

module _ (v X : Presheaf A ℓm) where
  powEv : 𝓟 [ v , X ^ (X ^ v) ]
  powEv .N-ob c p .N-ob d (g , α) = α .N-ob d (A.id , v .F-hom g p)
  powEv .N-ob c p .N-hom d' d k (g , α) (g' , α') e =
    α .N-hom d' d k (A.id , v .F-hom g p) _ refl
    ∙ cong₂ (λ h q → α .N-ob d' (h , q)) (A.⋆IdR k ∙ sym (A.⋆IdL k))
        (sym (funExt⁻ (v .F-seq g k) p) ∙ cong (λ m → v .F-hom m p) (cong fst e))
    ∙ (λ i → e i .snd .N-ob d' (A.id , v .F-hom g' p))
  powEv .N-hom c c' f p' p e = makePshHomStrictPath (funExt λ d → funExt λ (g , α) →
    cong (λ q → α .N-ob d (A.id , q)) (funExt⁻ (v .F-seq f g) p' ∙ cong (v .F-hom g) e))

  pshPower : EnrichedPower selfEnrichment v X
  pshPower .fst .vertex = X ^ v
  pshPower .fst .element = powEv
  pshPower .fst .universal W = isoToIsEquiv (iso _ curryPow
    (λ t → makePshHomStrictPath (funExt λ c → funExt λ p → makePshHomStrictPath
      (funExt λ d → funExt λ (g , w) →
          cong (λ m → t .N-ob d (v .F-hom m p) .N-ob d (A.id , W .F-hom A.id w)) (A.⋆IdL g)
        ∙ cong (λ q → t .N-ob d (v .F-hom g p) .N-ob d (A.id , q)) (funExt⁻ (W .F-id) w)
        ∙ sym (cong (λ φ → φ .N-ob d (A.id , w)) (t .N-hom d c g p _ refl))
        ∙ cong (λ m → t .N-ob c p .N-ob d (m , w)) (A.⋆IdL g))))
    (λ f → makePshHomStrictPath (funExt λ c → funExt λ w → makePshHomStrictPath
      (funExt λ d → funExt λ (g , p) →
          cong (λ q → f .N-ob d (W .F-hom g w) .N-ob d (A.id , v .F-hom q p)) (A.⋆IdL A.id)
        ∙ cong (λ q → f .N-ob d (W .F-hom g w) .N-ob d (A.id , q)) (funExt⁻ (v .F-id) p)
        ∙ sym (cong (λ φ → φ .N-ob d (A.id , p)) (f .N-hom d c g w _ refl))
        ∙ cong (λ m → f .N-ob c w .N-ob d (m , p)) (A.⋆IdL g)))))
    where
    curryPow : 𝓟 [ v , X ^ W ] → 𝓟 [ W , X ^ v ]
    curryPow t .N-ob c w .N-ob d (g , p) = t .N-ob d p .N-ob d (A.id , W .F-hom g w)
    curryPow t .N-ob c w .N-hom d' d k (g , p) (g' , p') e =
      t .N-ob d p .N-hom d' d k (A.id , W .F-hom g w) _ refl
      ∙ cong₂ (λ h q → t .N-ob d p .N-ob d' (h , q)) (A.⋆IdR k ∙ sym (A.⋆IdL k))
          (sym (funExt⁻ (W .F-seq g k) w) ∙ cong (λ m → W .F-hom m w) (cong fst e))
      ∙ cong (λ φ → φ .N-ob d' (A.id , W .F-hom g' w)) (t .N-hom d' d k p _ refl)
      ∙ cong (λ q → t .N-ob d' q .N-ob d' (A.id , W .F-hom g' w)) (cong snd e)
    curryPow t .N-hom c c' f w' w e = makePshHomStrictPath (funExt λ d → funExt λ (g , p) →
      cong (λ q → t .N-ob d p .N-ob d (A.id , q)) (funExt⁻ (W .F-seq f g) w' ∙ cong (W .F-hom g) e))
  pshPower .snd W U = isoToIsEquiv (iso _ uncurryPow
    (λ σ → makePshHomStrictPath (funExt λ c → funExt λ (u , p) → makePshHomStrictPath
      (funExt λ d → funExt λ (g , w) →
          cong₂ (λ m n → σ .N-ob d (U .F-hom m u , v .F-hom n p) .N-ob d (A.id , W .F-hom A.id w))
            (A.⋆IdL _ ∙ A.⋆IdL g) (A.⋆IdL g)
        ∙ cong (λ q → σ .N-ob d (U .F-hom g u , v .F-hom g p) .N-ob d (A.id , q)) (funExt⁻ (W .F-id) w)
        ∙ sym (cong (λ φ → φ .N-ob d (A.id , w)) (σ .N-hom d c g (u , p) _ refl))
        ∙ cong (λ m → σ .N-ob c (u , p) .N-ob d (m , w)) (A.⋆IdL g))))
    (λ h → makePshHomStrictPath (funExt λ c → funExt λ u → makePshHomStrictPath
      (funExt λ d → funExt λ (g , w) → makePshHomStrictPath (funExt λ e → funExt λ (k , p) →
          cong (λ φ → φ .N-ob e (A.id A.⋆ A.id , W .F-hom k w) .N-ob e (A.id , v .F-hom (A.id A.⋆ A.id) p))
            (sym (h .N-hom e c (k A.⋆ g) u _ refl))
        ∙ cong (λ m → h .N-ob c u .N-ob e (m , W .F-hom k w) .N-ob e (A.id , v .F-hom (A.id A.⋆ A.id) p))
            (cong (A._⋆ (k A.⋆ g)) (A.⋆IdL A.id) ∙ A.⋆IdL (k A.⋆ g))
        ∙ sym (cong (λ φ → φ .N-ob e (A.id , v .F-hom (A.id A.⋆ A.id) p))
            (h .N-ob c u .N-hom e d k (g , w) _ refl))
        ∙ cong₂ (λ m q → h .N-ob c u .N-ob d (g , w) .N-ob e (m , q))
            (A.⋆IdL k) (cong (λ m → v .F-hom m p) (A.⋆IdL A.id) ∙ funExt⁻ (v .F-id) p))))))
    where
    uncurryPow : _ → _
    uncurryPow σ .N-ob c u .N-ob d (g , w) .N-ob e (k , p) =
      σ .N-ob e (U .F-hom (k A.⋆ g) u , p) .N-ob e (A.id , W .F-hom k w)
    uncurryPow σ .N-ob c u .N-ob d (g , w) .N-hom e' e k' (k , p) (k₂ , p₂) eq =
      σ .N-ob e (U .F-hom (k A.⋆ g) u , p) .N-hom e' e k' (A.id , W .F-hom k w) _ refl
      ∙ cong (λ h → σ .N-ob e (U .F-hom (k A.⋆ g) u , p) .N-ob e' (h , W .F-hom k' (W .F-hom k w)))
          (A.⋆IdR k' ∙ sym (A.⋆IdL k'))
      ∙ cong (λ φ → φ .N-ob e' (A.id , W .F-hom k' (W .F-hom k w)))
          (σ .N-hom e' e k' (U .F-hom (k A.⋆ g) u , p) _ refl)
      ∙ cong₂ (λ m q → σ .N-ob e' m .N-ob e' (A.id , q))
          (ΣPathP ( sym (funExt⁻ (U .F-seq (k A.⋆ g) k') u)
                    ∙ cong (λ m → U .F-hom m u) (sym (A.⋆Assoc k' k g) ∙ cong (A._⋆ g) (cong fst eq))
                  , cong snd eq))
          (sym (funExt⁻ (W .F-seq k k') w) ∙ cong (λ m → W .F-hom m w) (cong fst eq))
    uncurryPow σ .N-ob c u .N-hom d' d k'' (g , w) (g' , w') eq = makePshHomStrictPath
      (funExt λ e → funExt λ (k , p) →
        cong₂ (λ m q → σ .N-ob e (U .F-hom m u , p) .N-ob e (A.id , q))
          (A.⋆Assoc k k'' g ∙ cong (k A.⋆_) (cong fst eq))
          (funExt⁻ (W .F-seq k'' k) w ∙ cong (W .F-hom k) (cong snd eq)))
    uncurryPow σ .N-hom c c' f u' u eq = makePshHomStrictPath (funExt λ d → funExt λ (g , w) →
      makePshHomStrictPath (funExt λ e → funExt λ (k , p) →
        cong (λ q → σ .N-ob e (q , p) .N-ob e (A.id , W .F-hom k w))
          (cong (λ m → U .F-hom m u') (sym (A.⋆Assoc _ _ _))
          ∙ funExt⁻ (U .F-seq f (k A.⋆ g)) u'
          ∙ cong (U .F-hom (k A.⋆ g)) eq)))
