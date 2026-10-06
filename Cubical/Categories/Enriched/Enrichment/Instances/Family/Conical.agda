{-# OPTIONS --lossy-unification #-}
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category

module Cubical.Categories.Enriched.Enrichment.Instances.Family.Conical
  {ℓ ℓ' : Level} (A : Category ℓ ℓ') (K : Category (ℓ-max ℓ ℓ') ℓ') (ℓS : Level) where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.StrictHom.Base
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Limits.AsRepresentable
open import Cubical.Categories.Monoidal.Instances.Presheaf.StrictHom
open import Cubical.Categories.Enriched.Enrichment.Limits.Conical
open import Cubical.Categories.Enriched.Enrichment.Instances.Power using (Setᴬ)
import Cubical.Categories.Enriched.Enrichment.Instances.Family.Limits as FamLimits

open Functor
open NatTrans
open PshHomStrict
open UniversalElement

private
  module A = Category A
open PshMon A ℓS using (ℓm)
private
  Fam = Setᴬ (A .Category.ob) ℓm
  famEnrichment = FamLimits.famEnrichment A ℓS

module _ (D : Functor K Fam) where
  private
    compatProp : ∀ a (x : ∀ k → ⟨ (D ⟅ k ⟆) a ⟩)
      → isProp (∀ {k k'} (m : K [ k , k' ]) → (D ⟪ m ⟫) a (x k) ≡ x k')
    compatProp a x = isPropImplicitΠ2 λ _ _ → isPropΠ λ _ → (D ⟅ _ ⟆) a .snd _ _

  limOb : Category.ob Fam
  limOb a = (Σ[ x ∈ (∀ k → ⟨ (D ⟅ k ⟆) a ⟩) ] (∀ {k k'} (m : K [ k , k' ]) → (D ⟪ m ⟫) a (x k) ≡ x k'))
    , isSetΣ (isSetΠ λ k → (D ⟅ k ⟆) a .snd) λ x → isProp→isSet (compatProp a x)

  limπ : NatTrans (ΔCone ⟅ limOb ⟆) D
  limπ .N-ob k a xx = xx .fst k
  limπ .N-hom m = funExt λ a → funExt λ xx → sym (xx .snd m)

  famLimit : EnrichedLimit famEnrichment D
  famLimit .fst .vertex = limOb
  famLimit .fst .element = limπ
  famLimit .fst .universal W = isoToIsEquiv (iso _ pair
    (λ c → makeNatTransPath (funExt λ k → refl))
    (λ f → funExt λ a → funExt λ w → Σ≡Prop (compatProp a) refl))
    where
    pair : NatTrans (ΔCone ⟅ W ⟆) D → Fam [ W , limOb ]
    pair c a w = (λ k → (c ⟦ k ⟧) a w) , λ m → sym (λ i → c .N-hom m i a w)
  famLimit .snd X U = isoToIsEquiv (iso _ pair
    (λ c → makeNatTransPath (funExt λ k → makePshHomStrictPath refl))
    (λ h → makePshHomStrictPath (funExt λ a → funExt λ u → funExt λ y → funExt λ g → funExt λ x →
      Σ≡Prop (compatProp y) refl)))
    where
    pair : _ → _
    pair c .N-ob a u y g x = (λ k → (c ⟦ k ⟧) .N-ob a u y g x)
      , λ m → sym (λ i → c .N-hom m i .N-ob a u y g x)
    pair c .N-hom a a' f u' u e = funExt λ y → funExt λ g → funExt λ x →
      Σ≡Prop (compatProp y) (funExt λ k → λ i → (c ⟦ k ⟧) .N-hom a a' f u' u e i y g x)
