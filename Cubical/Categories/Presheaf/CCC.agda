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
  ⊤𝓟 .vertex = Constant _ _ (Unit* , isSetUnit*)
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

module _ {C : Category ℓ ℓ'} {ℓA ℓB : Level} where
  module _ (P : Presheaf C ℓA) (Q : Presheaf C ℓB) where
    private
      module C = Category C
      module P = PresheafNotation P
      module Q = PresheafNotation Q
    -- ExpObFail0 : ob 𝓡
    -- ExpObFail0 .F-ob x .fst = P.p[ x ] → Q.p[ x ]
    -- ExpObFail0 .F-ob x .snd = {!!}
    -- ExpObFail0 .F-hom f α p = {!α!} -- fail! we can't get a Q.p[ y ] out of α, only Q.p[ x ]
    -- ExpObFail0 .F-id = {!!}
    -- ExpObFail0 .F-seq = {!!}

    -- ExpObFail1 : Presheaf C {!!}
    -- ExpObFail1 .F-ob x .fst = ∀ y (f : C [ y , x ]) → P.p[ y ] → Q.p[ y ]
    -- ExpObFail1 .F-ob x .snd = {!!}
    -- -- yay problem solved?
    -- ExpObFail1 .F-hom f α z g p = α z ((C ⋆ g) f) p
    -- ExpObFail1 .F-id = funExt λ α → funExt λ z → funExt λ g → funExt λ p →
    --   λ i → α z (C .⋆IdR g i) p
    -- -- Nope, can't prove F-seq without additional naturality assumption on α
    -- ExpObFail1 .F-seq f g = {!!}

    ExpOb : Presheaf C (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓA) ℓB)
    ExpOb .F-ob c .fst = PshHom (PshProd ⟅ (C [-, c ]) , P ⟆b) Q
    ExpOb .F-ob c .snd = isSetPshHom _ _
    ExpOb .F-hom f α .fst z (g , p) = α .fst z ((g C.⋆ f) , p)
    ExpOb .F-hom f α .snd z y h (g , p) =
      cong (α .fst z) (ΣPathP ((C.⋆Assoc _ _ _) , refl))
      ∙ α .snd z y h (g C.⋆ f , p)
    ExpOb .F-id = funExt λ α → makePshHomPath $ funExt λ z → funExt λ (g , p) →
      cong (α .fst z) (ΣPathP ((C.⋆IdR g) , refl))
    ExpOb .F-seq f g = funExt λ α → makePshHomPath $
      funExt λ z → funExt λ (h , p) →
      cong (α .fst z) (ΣPathP ((sym (C.⋆Assoc h g f)) , refl))

module _ (C : Category ℓ ℓ') (ℓS : Level) where
  private
    ℓS' = ℓ-max ℓ (ℓ-max ℓ' ℓS)
    module C = Category C

  -- inlining this definition results in termination checker issues..
  eval : (A B : Presheaf C ℓS') → PshProd ⟅ ExpOb A B , A ⟆b ⇒ B
  eval A B .N-ob x (α , a) = α .fst x (C.id , a)
  eval A B .N-hom f = funExt λ (α , a) →
    cong (α .fst _) (ΣPathP (C.⋆IdL f ∙ sym (C.⋆IdR f) , refl))
    ∙ α .snd _ _ _ _

  module _ (A B Γ : Presheaf C ℓS') where
    private
      module Γ = PresheafNotation Γ
    λPsh : PshProd ⟅ Γ , A ⟆b ⇒ B → Γ ⇒ ExpOb A B
    λPsh ϕ .N-ob x γ .fst y (f , a) = ϕ .N-ob y (f Γ.⋆ γ , a)
    λPsh ϕ .N-ob x γ .snd y z f (g , a) =
      cong (ϕ .N-ob y) (ΣPathP (Γ.⋆Assoc _ _ _ , refl))
      ∙ funExt⁻ (ϕ .N-hom _) _
    λPsh ϕ .N-hom f = funExt (λ γ → makePshHomPath (funExt (λ x → funExt (λ (g , a) → cong (ϕ .N-ob x) (ΣPathP ((sym $ Γ.⋆Assoc _ _ _) , refl))))))

  ⇒𝓟 : Exponentials (PresheafCategory C ℓS') (×𝓟 C _)
  ⇒𝓟 (P , Q) .vertex = ExpOb P Q
  ⇒𝓟 (P , Q) .element = eval P Q
  ⇒𝓟 (P , Q) .universal Γ = isIsoToIsEquiv
    ( λPsh P Q Γ
    , (λ α → makeNatTransPath (funExt (λ x → funExt (λ (f , p) → cong (α .N-ob x) (ΣPathP ((funExt⁻ (Γ .F-id) f) , refl))))))
    , λ α → makeNatTransPath (funExt (λ x → funExt (λ γ → makePshHomPath (funExt (λ y → funExt λ (f , p) →
      funExt⁻ (funExt⁻ (cong fst (funExt⁻ (α .N-hom f) γ)) y) _
      ∙ cong (α .N-ob x γ .fst y) (ΣPathP ((C.⋆IdL f) , refl))))))))
  open CartesianCategory renaming (C to Cat)
  open CartesianClosedCategory
  𝓟-CC : CartesianCategory _ _
  𝓟-CC .Cat = PresheafCategory C (ℓ-max ℓ (ℓ-max ℓ' ℓS))
  𝓟-CC .term = ⊤𝓟 _ _
  𝓟-CC .bp = ×𝓟 _ _

  𝓟-CCC : CartesianClosedCategory _ _
  𝓟-CCC .CC = 𝓟-CC
  𝓟-CCC .exps = Exponentials→AllExponentiable _ _ ⇒𝓟
