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
    module C = Category (SET ℓ)
    module Cᴰ = Categoryᴰ (SETᴰ ℓ ℓ')

    bp : (A : SET ℓ .ob) → BinProducts SETᴰ.v[ A ]
    bp A = BinProductsⱽ→BinProductsFibers (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ

    bpw : {A : Category.ob (SET ℓ)} → (Aᴰ Aᴰ' : SETᴰ.ob[ A ]) →
      UniversalElement SETᴰ.v[ A ] _
    bpw {A = A} Aᴰ =
      (BinProductsWithⱽ→BinProductsWithFiber (SETᴰ ℓ ℓ')
        (λ cᴰ' → BinProductsⱽSETᴰ A (cᴰ' , Aᴰ)))

  open Functor
  open UniversalElement
  FiberExponentialSETᴰ : (A : Category.ob (SET ℓ)) → (Aᴰ Aᴰ' : SETᴰ.ob[ A ]) →
    Exponential SETᴰ.v[ A ] Aᴰ Aᴰ' (bpw Aᴰ)
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .vertex a .fst = ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .vertex a .snd = isSet→ (str (Aᴰ' a))
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .element a (f , aᴰ) = f aᴰ
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .universal Aᴰ'' .equiv-proof f .fst .fst a aᴰ'' aᴰ = f a (aᴰ'' , aᴰ)
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .universal Aᴰ'' .equiv-proof f .fst .snd =
    fromPathP (λ i → transport-filler (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ × ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩) f (~ i))
  FiberExponentialSETᴰ A Aᴰ Aᴰ' .universal Aᴰ'' .equiv-proof f .snd (g , x) =
    ΣPathP (
      funExt₂ (λ a aᴰ'' → funExt λ aᴰ → sym (funExt⁻ (funExt⁻ x a) (aᴰ'' , aᴰ)))
      ∙ fromPathP (λ i → transport-filler (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ → ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩) g (~ i)) ,
      isSet→SquareP (λ _ _ → str (RightAdjointProf (BinProductWithF SETᴰ.v[ A ] (bpw Aᴰ)) .F-ob Aᴰ' .F-ob Aᴰ'')) _ _ _ _
      )

  open Exponentialⱽ
  ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .cᴰ⇒cᴰ' = FiberExponentialSETᴰ A Aᴰ Aᴰ'
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .reindex⇒ {b = B} f Bᴰ .equiv-proof gᴰ .fst .fst b bᴰ aᴰ = gᴰ b (bᴰ , aᴰ)
  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .reindex⇒ {b = B} f Bᴰ .equiv-proof gᴰ .fst .snd =
    λgᴰ PB.⋆ app'
      ≡⟨ {!!} ⟩
    (introCL CLAᴰ⇒Aᴰ' λgᴰ') PB.⋆ (α (Aᴰ ⇒A Aᴰ') ExpA.app)
      ≡⟨ {!sym $ α-natural ? ? ? ?!} ⟩
    {!!}
      ≡⟨ {!!} ⟩
    gᴰ
    ∎
    where
    f*F : Functor SETᴰ.v[ A ] SETᴰ.v[ B ]
    f*F = CartesianLiftF-fiber (SETᴰ ℓ ℓ') isFibrationSETᴰ f

    f*_ : SETᴰ.v[ A ] .ob → SETᴰ.v[ B ] .ob
    f*_ = f*F .F-ob

    module bpA = BinProductsNotation (bp A)
    module bpB = BinProductsNotation (bp B)

    _,pA_ = bpA._,p_
    _,pB_ = bpB._,p_
    _×A_ = bpA._×_
    _×pA_ = bpA._×p_
    _×B_ = bpB._×_
    _×pB_ = bpB._×p_

    module ExpA = ExponentialsNotation (bp A) (FiberExponentialSETᴰ A)
    module ExpB = ExponentialsNotation (bp B) (FiberExponentialSETᴰ B)

    _⇒A_ = ExpA._⇒_
    _⇒B_ = ExpB._⇒_

    CLAᴰ = isFibrationSETᴰ {c = B}{c' = A} Aᴰ f
    CLAᴰ' = isFibrationSETᴰ {c = B}{c' = A} Aᴰ' f
    CLAᴰ⇒Aᴰ' = isFibrationSETᴰ {c = B}{c' = A} (Aᴰ ⇒A Aᴰ') f
    module f*Aᴰ = CartesianLift CLAᴰ
    module f*Aᴰ' = CartesianLift CLAᴰ'
    module f*Aᴰ⇒Aᴰ' = CartesianLift CLAᴰ⇒Aᴰ'

    expPshA : Functor (SETᴰ.v[ A ] ^op) (SET (ℓ-max ℓ ℓ'))
    expPshA = ExponentiableProf SETᴰ.v[ A ] (bpw Aᴰ) .F-ob Aᴰ'

    expPshB : Functor (SETᴰ.v[ B ] ^op) (SET (ℓ-max ℓ ℓ'))
    expPshB = ExponentiableProf SETᴰ.v[ B ] (bpw (f* Aᴰ)) .F-ob (f* Aᴰ')

    module PA = PresheafNotation expPshA
    module PB = PresheafNotation expPshB

    --              λgᴰ
    --    Bᴰ -------------> f* (Aᴰ ⇒A Aᴰ')
    --    |                       |
    --    |                       |
    --    |                       |
    --    v                       v
    --    B --------------------> B
    --             id
    λgᴰ : SETᴰ.v[ B ] [ Bᴰ , f* (Aᴰ ⇒A Aᴰ') ]
    λgᴰ = ExpB.lda gᴰ

    λgᴰ' : Cᴰ.Hom[ f ][ Bᴰ , Aᴰ ⇒A Aᴰ' ]
    λgᴰ' = Cᴰ._⋆ᴰ_ {zᴰ = Aᴰ ⇒A Aᴰ'} λgᴰ f*Aᴰ⇒Aᴰ'.π

    λgᴰ≡ : λgᴰ ≡ introCL CLAᴰ⇒Aᴰ' λgᴰ'
    λgᴰ≡ = ηᴰCL CLAᴰ⇒Aᴰ'

    u : introCL CLAᴰ⇒Aᴰ' λgᴰ' ≡ {!!}
    u = {!!}

    -- precompλgᴰ×id : SETᴰ.v[ B ] [ (f* (Aᴰ ⇒A Aᴰ')) ×B (f* Aᴰ) , f* Aᴰ' ] →
    --                SETᴰ.v[ B ] [  Bᴰ ×B (f* Aᴰ) , f* Aᴰ' ]
    -- precompλgᴰ×id = expPshB .F-hom λgᴰ

    --                  gᴰ
    -- Bᴰ ×ⱽ f* Aᴰ -------------> Aᴰ'
    --    |                       |
    --    |                       |
    --    |                       |
    --    v                       v
    --    B --------------------> A
    --             f
    gᴰ' : (SETᴰ ℓ ℓ') [ f ][ Bᴰ ×B (f* Aᴰ) , Aᴰ' ]
    gᴰ' = gᴰ

    pshHom : PshHomᴰ f*F expPshA expPshB
    pshHom = preservesExpCone f*F (λ Aᴰ'' → bp A (Aᴰ'' , Aᴰ))
        (λ z →
           cartesianLift-preserves-BinProductFiber (SETᴰ ℓ ℓ') isFibrationSETᴰ
           (BinProductsⱽSETᴰ A (z , Aᴰ)) f)
        (bpw (f* Aᴰ)) Aᴰ'

    α : (Aᴰ'' : ob SETᴰ.v[ A ]) → PA.p[ Aᴰ'' ] → PB.p[ f* Aᴰ'' ]
    α = pshHom .fst

    α-natural : ∀ Aᴰ₁ Aᴰ₂ h x → α Aᴰ₁ (h PA.⋆ x) ≡ ((f*F .F-hom h) PB.⋆ α Aᴰ₂ x)
    α-natural = pshHom .snd

    app' : SETᴰ.v[ B ] [ (f* (Aᴰ ⇒A Aᴰ')) ×B (f* Aᴰ) , f* Aᴰ' ]
    app' = α (Aᴰ ⇒A Aᴰ') ExpA.app

    app'' : Cᴰ.Hom[ f ][ (f* (Aᴰ ⇒A Aᴰ')) ×B (f* Aᴰ) , Aᴰ' ]
    app'' = Cᴰ._⋆ᴰ_ {zᴰ = Aᴰ'} app' f*Aᴰ'.π

    app≡ : app' ≡ introCL CLAᴰ' app''
    app≡ = ηᴰCL CLAᴰ'

  ExponentialsⱽSETᴰ {c = A} Aᴰ Aᴰ' .reindex⇒ {b = B} f Bᴰ .equiv-proof gᴰ .snd = {!!}
