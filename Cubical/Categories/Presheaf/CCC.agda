{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Presheaf.CCC where

open import Cubical.Categories.Bifunctor
open import Cubical.Categories.Category
open import Cubical.Categories.Exponentials
open import Cubical.Categories.Functor.Base
open import Cubical.Categories.Functors.Constant
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.CartesianClosed.Base
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Yoneda.More

open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

private variable
  ℓ ℓ' : Level

open Category
open Functor
open Bifunctor
open NatTrans
open UniversalElement

module _ (C : Category ℓ ℓ') (ℓS : Level) where
  ⊤𝓟 : Terminal' (PresheafCategory C ℓS)
  ⊤𝓟 .vertex = LiftPsh UnitPsh ℓS
  ⊤𝓟 .element = tt
  ⊤𝓟 .universal _ = isIsoToIsEquiv
    ( (λ _ → natTrans (λ _ _ → tt*) (λ _ → refl))
    , (λ _ → refl)
    , (λ _ → makeNatTransPath refl))

  ×𝓟 : BinProducts (PresheafCategory C ℓS)
  ×𝓟 (P₁ , P₂) .vertex = PshProd ⟅ P₁ , P₂ ⟆b
  ×𝓟 (P₁ , P₂) .element .fst = natTrans ((λ _ (a , _) → a)) (λ _ → funExt λ{_ → refl})
  ×𝓟 (P₁ , P₂) .element .snd = natTrans (λ _ (_ , b) → b) λ _ → funExt λ{_ → refl}
  ×𝓟 (P₁ , P₂) .universal R = isIsoToIsEquiv
    ( (λ (f , g) →
      (natTrans (λ x z → f .N-ob x z , g .N-ob x z)
        (λ h → funExt λ z → ≡-×
          (funExt⁻ (f .N-hom h) z) (funExt⁻ (g .N-hom h) z))))
    , (λ _ → ΣPathP (makeNatTransPath refl , (makeNatTransPath refl)))
    , λ _ → makeNatTransPath (funExt λ x → funExt λ y → ΣPathP (refl , refl)))

module _ (C : Category ℓ ℓ') (ℓS : Level) where
  private
    module C = Category C
  ⇒𝓟 : AllExponentiable (PresheafCategory C (ℓ-max ℓ (ℓ-max ℓ' ℓS))) (×𝓟 C _)
  ⇒𝓟 P Q .vertex = P ⇒PshLarge Q
  ⇒𝓟 P Q .element = PshHom→NatTrans (appPshHom P Q)
  ⇒𝓟 P Q .universal S = isIsoToIsEquiv
    ( (λ f⟨p⟩ → PshHom→NatTrans (λPshHom _ _ (NatTrans→PshHom f⟨p⟩)))
    , (λ α → makeNatTransPath $ funExt (λ x → funExt (λ (f , p) → cong (α .N-ob x) (ΣPathP ((funExt⁻ (S .F-id) f) , refl)))))
    , (λ α → makeNatTransPath $ funExt (λ x → funExt (λ γ → makePshHomPath (funExt (λ y → funExt λ (f , p) →
      funExt⁻ (funExt⁻ (cong PshHom.N-ob (funExt⁻ (α .N-hom f) γ)) y) _
      ∙ cong (α .N-ob x γ .PshHom.N-ob y) (ΣPathP ((C.⋆IdL f) , refl)))))))
    )

  open CartesianCategory renaming (C to Cat)
  open CartesianClosedCategory
  𝓟-CC : CartesianCategory _ _
  𝓟-CC .Cat = PresheafCategory C (ℓ-max ℓ (ℓ-max ℓ' ℓS))
  𝓟-CC .term = ⊤𝓟 _ _
  𝓟-CC .bp = ×𝓟 _ _

  𝓟-CCC : CartesianClosedCategory _ _
  𝓟-CCC .CC = 𝓟-CC
  𝓟-CCC .exps = ⇒𝓟
