{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Family.Power
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Representable
import Cubical.Categories.Presheaf.Family.Base as FamBase
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Base
open import Cubical.Categories.Enriched.Enrichment.Limits.Power
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
open import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits A ℓS using (famEnrichment)

open Functor
open PshHomStrict
open UniversalElement
open PshMon A ℓS using (𝓟 ; ℓm)

private
  module A = Category A
  Fam = Setᴬ A.ob ℓm
  Uf = FamBase.PSH→Fam {ℓ = ℓS} A

module _ (v : Presheaf A ℓm) (X : Category.ob Fam) where
  powEv : 𝓟 [ v , famEnrichment .Enrichment.VE[_,_] (Uf ⟅ v ⟆ FamBase.⇒Fam X) X ]
  powEv .N-ob c p y h φ = φ (v .F-hom h p)
  powEv .N-hom c c' f p' p e = funExt λ y → funExt λ h → funExt λ φ →
    cong φ (funExt⁻ (v .F-seq f h) p' ∙ cong (v .F-hom h) e)

  famPower : EnrichedPower famEnrichment v X
  famPower .fst .vertex = Uf ⟅ v ⟆ FamBase.⇒Fam X
  famPower .fst .element = powEv
  famPower .fst .universal W = isoToIsEquiv (iso _ curryPow
    (λ t → makePshHomStrictPath (funExt λ c → funExt λ p → funExt λ y → funExt λ h → funExt λ w →
      sym (λ i → t .N-hom y c h p _ refl i y A.id w) ∙ cong (λ m → t .N-ob c p y m w) (A.⋆IdL h)))
    (λ f → funExt λ y → funExt λ w → funExt λ q → cong (f y w) (funExt⁻ (v .F-id) q)))
    where
    curryPow : 𝓟 [ v , famEnrichment .Enrichment.VE[_,_] W X ] → Fam [ W , Uf ⟅ v ⟆ FamBase.⇒Fam X ]
    curryPow t y w q = t .N-ob y q y A.id w
  famPower .snd W U = isoToIsEquiv (iso _ uncurryPow
    (λ σ → makePshHomStrictPath (funExt λ c → funExt λ (u , p) → funExt λ y → funExt λ g → funExt λ w →
      sym (λ i → σ .N-hom y c g (u , p) _ refl i y A.id w)
      ∙ cong (λ m → σ .N-ob c (u , p) y m w) (A.⋆IdL g)))
    (λ h → makePshHomStrictPath (funExt λ c → funExt λ u → funExt λ y → funExt λ g → funExt λ w →
      funExt λ q →
        cong (h .N-ob y (U .F-hom g u) y A.id w) (funExt⁻ (v .F-id) q)
        ∙ sym (λ i → h .N-hom y c g u _ refl i y A.id w q)
        ∙ cong (λ m → h .N-ob c u y m w q) (A.⋆IdL g))))
    where
    uncurryPow : _ → _
    uncurryPow σ .N-ob c u y g w q = σ .N-ob y (U .F-hom g u , q) y A.id w
    uncurryPow σ .N-hom c c' f u' u e = funExt λ y → funExt λ g → funExt λ w → funExt λ q →
      cong (λ x → σ .N-ob y (x , q) y A.id w) (funExt⁻ (U .F-seq f g) u' ∙ cong (U .F-hom g) e)
