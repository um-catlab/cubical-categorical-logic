{-# OPTIONS --safe --lossy-unification #-}
module Cubical.Categories.Displayed.Instances.Sets.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Adjoint.UniversalElements
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Sets.More
open import Cubical.Categories.Instances.Sets.Properties
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Exponentials

open import Cubical.Categories.Constructions.Fiber

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Exponentials.Base


private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open UniversalElementᴰ
open UniversalElementⱽ
open CartesianLift
open Categoryᴰ
open Category
open isIsoOver

isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
isFibrationSETᴰ {c = A}{c' = B} Bᴰ f .f*yᴰ a = Bᴰ (f a)
isFibrationSETᴰ cᴰ' f .CartesianLift.π = λ x z → z
isFibrationSETᴰ cᴰ' f .isCartesian .fst = λ z₁ → z₁
isFibrationSETᴰ cᴰ' f .isCartesian .snd .fst _ = refl
isFibrationSETᴰ cᴰ' f .isCartesian .snd .snd _ = refl

TerminalsⱽSETᴰ : Terminalsⱽ (SETᴰ ℓ ℓ')
TerminalsⱽSETᴰ A .vertexⱽ a = Unit* , isSetUnit*
TerminalsⱽSETᴰ A .elementⱽ = tt
TerminalsⱽSETᴰ A .universalⱽ .fst = λ _ x _ → tt*
TerminalsⱽSETᴰ A .universalⱽ .snd .fst b = refl
TerminalsⱽSETᴰ A .universalⱽ .snd .snd a = refl

BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
BinProductsⱽSETᴰ A (Aᴰ₁ , Aᴰ₂) .vertexⱽ a =
  (⟨ Aᴰ₁ a ⟩ × ⟨ Aᴰ₂ a ⟩) , (isSet× (Aᴰ₁ a .snd) (Aᴰ₂ a .snd))
BinProductsⱽSETᴰ A (Aᴰ₁ , Aᴰ₂) .elementⱽ = (λ _ → fst) , (λ _ → snd)
BinProductsⱽSETᴰ A (Aᴰ₁ , Aᴰ₂) .universalⱽ .fst x x₁ x₂ =
  x .fst x₁ x₂ , x .snd x₁ x₂
BinProductsⱽSETᴰ A (Aᴰ₁ , Aᴰ₂) .universalⱽ .snd .fst b =
  sym $ transport-filler _ _
-- the transports here are caused by the fact that vertical
-- composition is defined using reindexing :/ the only way to avoid
-- this would be to "fatten" the definition of displayed categories to
-- include the "redundant" vertical and heterogeneous compositions
-- then in the case of nice examples like SETᴰ (and possibly
-- PRESHEAFᴰ) we would get that there is no transport required
BinProductsⱽSETᴰ A (Aᴰ₁ , Aᴰ₂) .universalⱽ {y = B} {yᴰ = Bᴰ} {f} .snd .snd a =
  funExt₂ λ b bᴰ →
  ΣPathP
   ( fromPathP (λ i → a
       (transport-filler (λ _ → ⟨ B ⟩) b (~ i))
       (transport-filler (λ j₂ → fst (Bᴰ (transp (λ j₁ → fst B) (~ j₂) b)))
         bᴰ (~ i)) .fst)
   , fromPathP
     (λ i → a
       (transport-filler (λ _ → ⟨ B ⟩) b (~ i))
       (transport-filler (λ j₂ → fst (Bᴰ (transp (λ j₁ → fst B) (~ j₂) b)))
         bᴰ (~ i)) .snd))

SETᴰCartesianCategoryⱽ :
  ∀ ℓ ℓ' → CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.Cᴰ = SETᴰ ℓ ℓ'
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.termⱽ = TerminalsⱽSETᴰ
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.bpⱽ = BinProductsⱽSETᴰ
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.cartesianLifts = isFibrationSETᴰ

module _ {ℓ} {ℓ'} where
  private
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

    bp : (A : SET ℓ .ob) → BinProducts SETᴰ.v[ A ]
    bp A = BinProductsⱽ→BinProductsFibers (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ

    bpw : {A : SET ℓ .ob} → (Aᴰ : SETᴰ.ob[ A ]) → BinProductsWith SETᴰ.v[ A ] Aᴰ
    bpw {A = A} Aᴰ Aᴰ' = bp A (Aᴰ' , Aᴰ)

  open UniversalElement

  -- This isn't strictly necessary to build ExponentialsⱽSETᴰ
  -- We only need the vertex and element, however because the existing
  -- proof in ExponentialsⱽSETᴰ .becomes-universal uses β from this structure
  -- we are keeping this construction for now
  FiberExponentialSETᴰ : (A : SET ℓ .ob) → (Aᴰ Aᴰ' : SETᴰ.ob[ A ]) →
    Exponential SETᴰ.v[ A ] Aᴰ Aᴰ' (bpw Aᴰ)
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .vertex a .fst = ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .vertex a .snd = isSet→ (str (Aᴰ' a))
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .element a (f , aᴰ) = f aᴰ
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .universal Aᴰ'' =
    isIsoToIsEquiv (
      (λ f a aᴰ'' aᴰ → f a (aᴰ'' , aᴰ)) ,
      (λ f → fromPathP
        (λ i → transport-filler
          (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ × ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩) f (~ i))),
      (λ f  → fromPathP
        (λ i → transport-filler
          (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ → ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩) f (~ i))))

  private
    module _ (A : SET ℓ .ob)(Aᴰ Aᴰ' : SETᴰ.ob[ A ]) where
      module FibExp = ExponentialNotation (bpw Aᴰ) (FiberExponentialSETᴰ A Aᴰ Aᴰ')

  open Exponentialⱽ

  ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .vertex = FibExp.vert A Aᴰ Aᴰ'
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .element = FibExp.app A Aᴰ Aᴰ'
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .becomes-universal {b = B} f Bᴰ =
    isIsoToIsEquiv (
      (λ gᴰ b bᴰ faᴰ → gᴰ b (bᴰ , faᴰ)) ,
      (λ gᴰ →
        cong₂ (seq' SETᴰ.v[ B ]) refl (ExpB.⇒ue.β _ _)
        ∙ ExpB.⇒ue.β _ _
      ) ,
      (λ gᴰ → funExt₃ λ b bᴰ faᴰ →
        funExt⁻ (funExt⁻
          (cong₂ (seq' SETᴰ.v[ B ]) refl (ExpB.⇒ue.β _ _) ∙ ExpB.⇒ue.β _ _)
        b) (bᴰ , faᴰ))
    )
    where
    module ExpB = ExponentialsNotation (bp B) (FiberExponentialSETᴰ B)
