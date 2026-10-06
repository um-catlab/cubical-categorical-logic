{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Conical
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (K : Category (ℓ-max ℓ ℓ') ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical
import Cubical.Categories.Enriched.Enrichment.Instances.Presheaf.StrictHom.Self as Self

open Functor
open NatTrans
open PshHomStrict
open UniversalElement

private
  module A = Category A
  module K = Category K
open PshMon A ℓS using (𝓟 ; ℓm)

module _ (D : Functor K 𝓟) where
  private
    compatProp : ∀ c (x : ∀ k → ⟨ (D ⟅ k ⟆) .F-ob c ⟩)
      → isProp (∀ {k k'} (m : K [ k , k' ]) → (D ⟪ m ⟫) .N-ob c (x k) ≡ x k')
    compatProp c x = isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → (D ⟅ _ ⟆) .F-ob c .snd _ _

  limOb : Presheaf A ℓm
  limOb .F-ob c = (Σ[ x ∈ (∀ k → ⟨ (D ⟅ k ⟆) .F-ob c ⟩) ]
      (∀ {k k'} (m : K [ k , k' ]) → (D ⟪ m ⟫) .N-ob c (x k) ≡ x k'))
    , isSetΣ (isSetΠ λ k → (D ⟅ k ⟆) .F-ob c .snd) λ x → isProp→isSet (compatProp c x)
  limOb .F-hom f (x , cx) = (λ k → (D ⟅ k ⟆) .F-hom f (x k))
    , λ m → sym ((D ⟪ m ⟫) .N-hom _ _ f (x _) _ refl) ∙ cong ((D ⟅ _ ⟆) .F-hom f) (cx m)
  limOb .F-id = funExt λ (x , cx) → Σ≡Prop (compatProp _) (funExt λ k → funExt⁻ ((D ⟅ k ⟆) .F-id) (x k))
  limOb .F-seq f g = funExt λ (x , cx) →
    Σ≡Prop (compatProp _) (funExt λ k → funExt⁻ ((D ⟅ k ⟆) .F-seq f g) (x k))

  limπ : NatTrans (ΔCone ⟅ limOb ⟆) D
  limπ .N-ob k = pshhom (λ c xx → xx .fst k) (λ c c' f xx' xx e → cong (λ y → y .fst k) e)
  limπ .N-hom m = makePshHomStrictPath (funExt λ c → funExt λ xx → sym (xx .snd m))

  pshLimit : EnrichedLimit (Self.selfEnrichment A ℓS) D
  pshLimit .fst .vertex = limOb
  pshLimit .fst .element = limπ
  pshLimit .fst .universal W = isoToIsEquiv (iso _ pair
    (λ c → makeNatTransPath (funExt λ k → makePshHomStrictPath refl))
    (λ f → makePshHomStrictPath (funExt λ a → funExt λ w → Σ≡Prop (compatProp a) refl)))
    where
    pair : NatTrans (ΔCone ⟅ W ⟆) D → PshHomStrict W limOb
    pair c .N-ob a w = (λ k → (c ⟦ k ⟧) .N-ob a w)
      , λ m → sym (cong (λ φ → φ .N-ob a w) (c .N-hom m))
    pair c .N-hom a a' f w' w e = Σ≡Prop (compatProp _) (funExt λ k → (c ⟦ k ⟧) .N-hom a a' f w' w e)
  pshLimit .snd X U = isoToIsEquiv (iso _ pair
    (λ c → makeNatTransPath (funExt λ k → makePshHomStrictPath (funExt λ a → funExt λ u →
      makePshHomStrictPath (funExt λ d → funExt λ (g , x) →
        cong (λ m → (c ⟦ k ⟧) .N-ob a u .N-ob d (m , x)) (A.⋆IdL g)))))
    (λ h → makePshHomStrictPath (funExt λ a → funExt λ u → makePshHomStrictPath
      (funExt λ d → funExt λ (g , x) → Σ≡Prop (compatProp d)
        (funExt λ k → cong (λ m → h .N-ob a u .N-ob d (m , x) .fst k) (A.⋆IdL g))))))
    where
    pair : _ → _
    pair c .N-ob a u .N-ob d (g , x) = (λ k → (c ⟦ k ⟧) .N-ob a u .N-ob d (g , x))
      , λ m → sym (cong (λ φ → φ .N-ob a u .N-ob d (g , x)) (c .N-hom m)
                   ∙ cong (λ n → (D ⟪ m ⟫) .N-ob d ((c ⟦ _ ⟧) .N-ob a u .N-ob d (n , x))) (A.⋆IdL g))
    pair c .N-ob a u .N-hom d' d f gx gx' e =
      Σ≡Prop (compatProp _) (funExt λ k → (c ⟦ k ⟧) .N-ob a u .N-hom d' d f gx gx' e)
    pair c .N-hom a a' f u' u e = makePshHomStrictPath (funExt λ d → funExt λ gx →
      Σ≡Prop (compatProp _) (funExt λ k → λ i → (c ⟦ k ⟧) .N-hom a a' f u' u e i .N-ob d gx))
