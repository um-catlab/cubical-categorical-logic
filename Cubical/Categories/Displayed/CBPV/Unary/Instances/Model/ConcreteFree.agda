{-# OPTIONS --prop --lossy-unification #-}
module Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.ConcreteFree where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Isomorphism.More
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure


open import Cubical.Algebra.Theory.Base
  hiding (ℓ; ℓᴰ; ℓᴰᴰ; ℓ'; ℓᴰ'; ℓᴰᴰ'; ℓ''; ℓᴰ''; ℓO; ℓA; ℓE)

open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Category
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.TotalCategory
open import Cubical.Categories.Instances.WalkingArrow
  renaming (l to 𝒱; r to 𝒞)
open import Cubical.Categories.Presheaf.Representable

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Algebra.Model
open import Cubical.Categories.Displayed.Instances.Algebra.DisplayedModel
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Instances.Model.Multiplicative

open Category
open UniversalElement

private
  variable
    ℓO ℓA ℓE ℓEA : Level

module _ (T : Theory ℓO ℓA ℓE ℓEA) where
  open Theory T

  private
    L = ModelLevel T

  FreeRestriction :
    (FreeModel : hSet L → Model L)
    (η : (A : hSet L) → ⟨ A ⟩ → ⟨ FreeModel A .fst ⟩)
    (A : hSet L) (B : Model L) →
    Homo (Model→Algebra (FreeModel A)) (Model→Algebra B) → ⟨ A ⟩ → ⟨ B .fst ⟩
  FreeRestriction FreeModel η A B ϕ x = ϕ .fst (η A x)

  FreeRestrictionᴰ :
    (FreeModel : hSet L → Model L)
    (η : (A : hSet L) → ⟨ A ⟩ → ⟨ FreeModel A .fst ⟩)
    (FreeModelᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L) →
      Modelᴰ (FreeModel A) L)
    (ηᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      (x : ⟨ A ⟩) → ⟨ Aᴰ x ⟩ →
      ⟨ FreeModelᴰ A Aᴰ .fst (η A x) ⟩)
    (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
    {B : Model L} (ϕ : Homo (Model→Algebra (FreeModel A)) (Model→Algebra B))
    (Bᴰ : Modelᴰ B L) →
    Homoᴰ ϕ (Modelᴰ→Algebraᴰ (FreeModel A) (FreeModelᴰ A Aᴰ))
      (Modelᴰ→Algebraᴰ B Bᴰ) →
    (x : ⟨ A ⟩) → ⟨ Aᴰ x ⟩ →
      ⟨ Bᴰ .fst (ϕ .fst (η A x)) ⟩
  FreeRestrictionᴰ FreeModel η FreeModelᴰ ηᴰ A Aᴰ ϕ Bᴰ ϕᴰ x xᴰ =
    ϕᴰ .fst (η A x) (ηᴰ A Aᴰ x xᴰ)

  module _
    (FreeModel : hSet L → Model L)
    (η : (A : hSet L) → ⟨ A ⟩ → ⟨ FreeModel A .fst ⟩)
    (FreeUniversal : (A : hSet L) (B : Model L) →
      isEquiv (FreeRestriction FreeModel η A B))
    (FreeModelᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L) →
      Modelᴰ (FreeModel A) L)
    (ηᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      (x : ⟨ A ⟩) → ⟨ Aᴰ x ⟩ →
      ⟨ FreeModelᴰ A Aᴰ .fst (η A x) ⟩)
    (FreeUniversalᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L)
      {B : Model L} (ϕ : Homo (Model→Algebra (FreeModel A)) (Model→Algebra B))
      (Bᴰ : Modelᴰ B L) →
      isEquiv
        (FreeRestrictionᴰ FreeModel η FreeModelᴰ ηᴰ A Aᴰ ϕ Bᴰ))
    where

    ConcreteFreeMODEL : hSet L → Category.ob (MODEL T L)
    ConcreteFreeMODEL A = FreeModel A

    ConcreteMODELFree : LeftAdjoint (MODELForget T)
    ConcreteMODELFree A .vertex = ConcreteFreeMODEL A
    ConcreteMODELFree A .element = η A
    ConcreteMODELFree A .universal B =
      FreeUniversal A B

    private
      ConcreteFreeMODELᴰ : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L) →
        Categoryᴰ.ob[_] (MODELᴰ T L L) (ConcreteFreeMODEL A)
      ConcreteFreeMODELᴰ A Aᴰ = FreeModelᴰ A Aᴰ

      C = ModelCBPVWithFree T ConcreteMODELFree .fst
      Cᴰ = ModelCBPVᴰWithFree T ConcreteMODELFree

      η-lift : (A : hSet L) (Aᴰ : ⟨ A ⟩ → hSet L) →
        CartesianLift (Cᴰ ^opᴰᴰ)
          (FreeMODELη T ConcreteMODELFree A) Aᴰ
      η-lift A Aᴰ = UniversalElementⱽ'.REPRⱽ ue
        where
        module Cᴰᶠ = Fibers (Cᴰ ^opᴰᴰ)
        module Dᴰ = Fibers (MODELᴰ T L L)

        ue : UniversalElementⱽ' (Cᴰ ^opᴰᴰ)
          (𝒞 , ConcreteFreeMODEL A)
          (CartesianLiftPshSpec
            ((∫C (C ^opᴰ)) [-, (𝒱 , A) ])
            (Cᴰ ^opᴰᴰ)
            ((Cᴰ ^opᴰᴰ) [-][-, Aᴰ ])
            (FreeMODELη T ConcreteMODELFree A))
        ue .UniversalElementⱽ'.vertexⱽ = ConcreteFreeMODELᴰ A Aᴰ
        ue .UniversalElementⱽ'.elementⱽ = ηᴰ A Aᴰ
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒱 , Z) , Zᴰ , ()) .fst
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ϕ) .fst ıᴰ =
            isEquivToIsIso _
              (FreeUniversalᴰ A Aᴰ (ϕ .snd) Zᴰ)
              .fst ıᴰ
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒱 , Z) , Zᴰ , ()) .snd .fst
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ϕ) .snd .fst ıᴰ =
            Cᴰᶠ.rectifyOut {e' = refl}
              ( Cᴰᶠ.reind-filler⁻ _
              ∙ Cᴰᶠ.≡in {pth = refl}
                  (isEquivToIsIso _
                    (FreeUniversalᴰ A Aᴰ
                      (ϕ .snd) Zᴰ)
                    .snd .fst ıᴰ))
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒱 , Z) , Zᴰ , ()) .snd .snd
        ue .UniversalElementⱽ'.universalⱽ
          ((𝒞 , Z) , Zᴰ , ϕ) .snd .snd ϕᴰ =
            cong (ue .UniversalElementⱽ'.universalⱽ
              ((𝒞 , Z) , Zᴰ , ϕ) .fst)
              (Cᴰᶠ.rectifyOut {e' = refl} (Cᴰᶠ.reind-filler⁻ _))
            ∙ (Dᴰ.rectify $ Dᴰ.≡out $
                Dᴰ.≡in {pth = refl}
                  (isEquivToIsIso _
                    (FreeUniversalᴰ A Aᴰ
                      (ϕ .snd) Zᴰ)
                    .snd .snd ϕᴰ))

    ConcreteFreeMODELConstruction : FreeMODELConstruction T
    ConcreteFreeMODELConstruction .fst = ConcreteMODELFree
    ConcreteFreeMODELConstruction .snd = η-lift
