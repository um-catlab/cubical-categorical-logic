{-# OPTIONS --lossy-unification #-}
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
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.More

open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
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
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Exponentials

open import Cubical.Categories.Constructions.Fiber hiding (fiber)

open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Fibration.Base
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf
open import Cubical.Categories.Displayed.Presheaf.CartesianLift
  using () renaming (CartesianLift to PshᴰCartesianLift)
open import Cubical.Categories.Displayed.Limits.Cartesian
open import Cubical.Categories.Displayed.Limits.BinProduct
open import Cubical.Categories.Displayed.Limits.BinProduct.Fiberwise
open import Cubical.Categories.Displayed.Limits.Terminal
open import Cubical.Categories.Displayed.Exponentials.Base
open import Cubical.Categories.Displayed.Quantifiers

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open UniversalElementᴰ
open UniversalElementⱽ
open Categoryᴰ
open Category
open isIsoOver

isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
isFibrationSETᴰ Q f .vertexⱽ a = Q (f a)
isFibrationSETᴰ Q f .elementⱽ _ q = q
isFibrationSETᴰ Q f .universalⱽ .fst = λ z → z
isFibrationSETᴰ Q f .universalⱽ .snd .fst b =
  transportRefl _ ∙ transportRefl _
isFibrationSETᴰ Q f .universalⱽ .snd .snd a =
  transportRefl _ ∙ transportRefl _

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
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.Cᴰ =
  SETᴰ ℓ ℓ'
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.termⱽ =
  TerminalsⱽSETᴰ
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.bpⱽ =
  BinProductsⱽSETᴰ
SETᴰCartesianCategoryⱽ ℓ ℓ' .CartesianCategoryⱽ.cartesianLifts =
  isFibrationSETᴰ

module _ {ℓ} {ℓ'} where
  private
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

    bp : (A : SET ℓ .ob) → BinProducts SETᴰ.v[ A ]
    bp A = BinProductsⱽ→BinProductsFibers (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ

    bpw : {A : SET ℓ .ob} → (Aᴰ : SETᴰ.ob[ A ]) →
      BinProductsWith SETᴰ.v[ A ] Aᴰ
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
          (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ × ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩)
          f (~ i))),
      (λ f  → fromPathP
        (λ i → transport-filler
          (λ j → (a : ⟨ A ⟩) → ⟨ Aᴰ'' a ⟩ → ⟨ Aᴰ a ⟩ → ⟨ Aᴰ' a ⟩)
          f (~ i))))

  private
    module _ (A : SET ℓ .ob)(Aᴰ Aᴰ' : SETᴰ.ob[ A ]) where
      module FibExp = ExponentialNotation (bpw Aᴰ) (FiberExponentialSETᴰ A Aᴰ Aᴰ')

-- This is really slow
ExponentialsⱽSETᴰ :
  Exponentialsⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ
ExponentialsⱽSETᴰ {c = A} P Q .vertexⱽ a .fst = ⟨ P a ⟩ → ⟨ Q a ⟩
ExponentialsⱽSETᴰ {c = A} P Q .vertexⱽ a .snd = isSet→ (Q a .snd)
ExponentialsⱽSETᴰ {c = A} P Q .elementⱽ a x = x .fst (x .snd)
ExponentialsⱽSETᴰ {c = A} P Q .universalⱽ .fst f γ γᴰ p = f γ (γᴰ , p)
ExponentialsⱽSETᴰ {ℓ}{ℓ'}{A} P Q .universalⱽ {Γ} {Γᴰ} {f} .snd .fst fᴰ =
  funExt λ γ → funExt λ γᴰ →
  -- nasty. avoidable?
  -- Disgusting, but filling all these paths in helps performance
  Q.Prectify $ Q.≡out $ sym $
    cong₂fᴰ
      (Γᴰ.reind-filler (λ i → transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0 ∨ ~ i) γ)
        ∙ Γᴰ.reind-filler λ i → transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0 ∨ ~ i) (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0) γ))
      (P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) γ))
        ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 γ)))
        ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ))))
        ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ)))))
        ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ)))))
        ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ))))
        ∙ P.reind-filler (λ i → PresheafNotation.⋆IdL (SET ℓ [-, A ]) ((SET ℓ [-, A ]) .Functor.F-hom f (id (SET ℓ))) i (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i) (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0) γ)))
        ∙ P.reind-filler λ i → ⋆IdL (SET ℓ) f (i0 ∨ ~ i) (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0 ∨ ~ i) (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0) γ)))
      ∙ Q.reind-filler (λ i → ⋆IdL (SET ℓ) f i (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i) (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i0) γ)))
      ∙ Q.reind-filler λ i → ⋆IdR (SET ℓ) f i (transp (λ j → ⟨ Γ ⟩) (i0 ∨ i) γ)
  where
    ⟨P⟩ ⟨Q⟩ : ⟨ A ⟩ → Type _
    ⟨Q⟩ a = ⟨ Q a ⟩
    ⟨P⟩ a = ⟨ P a ⟩
    ⟨Γᴰ⟩ : ⟨ Γ ⟩ → Type _
    ⟨Γᴰ⟩ γ = ⟨ Γᴰ γ ⟩
    module P = hSetReasoning A ⟨P⟩
    module Q = hSetReasoning A ⟨Q⟩
    module Γᴰ = hSetReasoning Γ ⟨Γᴰ⟩

    cong₂fᴰ :
      ∀ {γ γ'}{γᴰ γᴰ'}{p p'}
        (γᴰ≡γᴰ' : Path (Σ ⟨ Γ ⟩ ⟨Γᴰ⟩) (γ , γᴰ) (γ' , γᴰ'))
      → (p≡p' : Path (Σ ⟨ A ⟩ ⟨P⟩) (f γ , p) (f γ' , p'))
      → Path (Σ ⟨ A ⟩ ⟨Q⟩) (f γ , fᴰ γ (γᴰ , p)) (f γ' , fᴰ γ' (γᴰ' , p'))
    cong₂fᴰ γᴰ≡γᴰ' p≡p' i = (f (γᴰ≡γᴰ' i .fst)) , (fᴰ (γᴰ≡γᴰ' i .fst) ((γᴰ≡γᴰ' i .snd)
      , (P.Prectify {e = cong fst p≡p'}{e' = cong f $ cong fst γᴰ≡γᴰ'}(λ j → p≡p' j .snd) i)))

ExponentialsⱽSETᴰ {ℓ} {ℓ'} {c = A} P Q .universalⱽ {Γ} {Γᴰ} {f} .snd .snd fᴰ =
  funExt λ γ → funExt λ γᴰ → funExt λ p →
  Q.Prectify $ Q.≡out $ sym $
    cong₃fᴰ
      (Γᴰ.reind-filler (λ i → transp (λ j → fst Γ) (~ i) γ)
      ∙ Γᴰ.reind-filler λ i → transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 γ))
      (P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) γ))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 γ)))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ))))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ)))))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ)))))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 (transp (λ j → fst Γ) i0 γ))))
      ∙ P.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 γ)))
      ∙ P.reind-filler λ i → f (transp (λ j → fst Γ) (~ i) (transp (λ j → fst Γ) i0 γ)))
    ∙ Q.reind-filler (λ i → f (transp (λ j → fst Γ) i (transp (λ j → fst Γ) i0 γ)))
    ∙ Q.reind-filler λ i → f (transp (λ j → fst Γ) i γ)
  where
    ⟨P⟩ ⟨Q⟩ : ⟨ A ⟩ → Type _
    ⟨Q⟩ a = ⟨ Q a ⟩
    ⟨P⟩ a = ⟨ P a ⟩
    ⟨Γᴰ⟩ : ⟨ Γ ⟩ → Type _
    ⟨Γᴰ⟩ γ = ⟨ Γᴰ γ ⟩
    module P = hSetReasoning A ⟨P⟩
    module Q = hSetReasoning A ⟨Q⟩
    module Γᴰ = hSetReasoning Γ ⟨Γᴰ⟩

    cong₃fᴰ :
      ∀ {γ γ'}{γᴰ γᴰ'}{p p'}
        (γᴰ≡γᴰ' : Path (Σ ⟨ Γ ⟩ ⟨Γᴰ⟩) (γ , γᴰ) (γ' , γᴰ'))
      → (p≡p' : Path (Σ ⟨ A ⟩ ⟨P⟩) (f γ , p) (f γ' , p'))
      → Path (Σ ⟨ A ⟩ ⟨Q⟩) (f γ , fᴰ γ γᴰ p) (f γ' , fᴰ γ' γᴰ' p')
    cong₃fᴰ γᴰ≡γᴰ' p≡p' i .fst = (f (γᴰ≡γᴰ' i .fst))
    cong₃fᴰ γᴰ≡γᴰ' p≡p' i .snd =
      fᴰ _ ((γᴰ≡γᴰ' i .snd))
        ((P.Prectify {e = cong fst p≡p'}{e' = cong f $ cong fst γᴰ≡γᴰ'}(λ j → p≡p' j .snd) i))

module _ {ℓ} {ℓ'} where
  private
    module SET = Category (SET ℓ)
    module SETᴰ = Fibers (SETᴰ ℓ (ℓ-max ℓ ℓ'))
    bp = BinProductsSET {ℓSET = ℓ}
    module bp = BinProductsNotation bp
  module _ {A B : SET.ob} (C : SETᴰ.ob[ A bp.× B ]) where
    private
      -×B = BinProducts→BinProductsWith (SET ℓ) B bp
      module -×B = BinProductsWithNotation -×B

    UniversalQuantifierSETᴰ :
      UniversalQuantifier -×B (λ D → isFibrationSETᴰ D fst) C
    UniversalQuantifierSETᴰ .vertexⱽ a .fst =
      ∀ (b : ⟨ B ⟩) → ⟨ C (a , b) ⟩
    UniversalQuantifierSETᴰ .vertexⱽ a .snd =
      isSetΠ (λ _ → str (C _))
    UniversalQuantifierSETᴰ .elementⱽ (a , b) c = c b
    UniversalQuantifierSETᴰ .universalⱽ .fst fᴰ d dᴰ b =
      fᴰ (d , b) dᴰ
    UniversalQuantifierSETᴰ .universalⱽ {y = D} {yᴰ = Dᴰ} {f = f} .snd .fst fᴰ =
      funExt₂ $ λ (d , b) dᴰ →
        C.Prectify $ C.≡out $ sym $
          cong₂fᴰ
            (sym $
              (λ i → transp (λ _ → ⟨ B ⟩) i
                      (transp (λ _ → ⟨ B ⟩) i0
                        (transp (λ _ → ⟨ B ⟩) i0 b)))
              ∙ (λ i → transp (λ _ → ⟨ B ⟩) i
                        (transp (λ _ → ⟨ B ⟩) i0 b))
              ∙ λ i → transp (λ _ → ⟨ B ⟩) i b)
            (Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) d)
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 d))
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d)))
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d))))
              ∙ Dᴰ.reind-filler λ i → transp (λ i₁ → D .fst) i (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d))))
          ∙ C.reind-filler _
          ∙ C.reind-filler _
          ∙ C.reind-filler _
      where
      ⟨C⟩ : ⟨ A bp.× B ⟩ → Type _
      ⟨C⟩ ab = ⟨ C ab ⟩

      ⟨Dᴰ⟩ : ⟨ D ⟩ → Type _
      ⟨Dᴰ⟩ d = ⟨ Dᴰ d ⟩

      module C = hSetReasoning (A bp.× B) ⟨C⟩
      module Dᴰ = hSetReasoning D ⟨Dᴰ⟩

      cong₂fᴰ : ∀ {b b'} {d d'} {dᴰ dᴰ'} →
        (b≡b' : b ≡ b') →
        (dᴰ≡dᴰ' : (d , dᴰ) ≡ (d' , dᴰ')) →
        Path (Σ ⟨ A bp.× B ⟩ ⟨C⟩)
         ((f d , b) , fᴰ (d , b) dᴰ)
         ((f d' , b') , fᴰ (d' , b') dᴰ')
      cong₂fᴰ b≡b' dᴰ≡dᴰ' i =
        ((f (dᴰ≡dᴰ' i .fst)) , (b≡b' i)) ,
        (fᴰ (dᴰ≡dᴰ' i .fst , (b≡b' i)) (dᴰ≡dᴰ' i .snd))

    UniversalQuantifierSETᴰ .universalⱽ {y = D} {yᴰ = Dᴰ} {f = f} .snd .snd fᴰ =
      funExt₃ λ d dᴰ b →
        C.Prectify $ C.≡out $ sym $
          cong₃fᴰ
            (sym $
              (λ i → transp (λ _ → ⟨ B ⟩) i
                      (transp (λ _ → ⟨ B ⟩) i0
                        (transp (λ _ → ⟨ B ⟩) i0 b)))
              ∙ (λ i → transp (λ _ → ⟨ B ⟩) i
                        (transp (λ _ → ⟨ B ⟩) i0 b))
              ∙ λ i → transp (λ _ → ⟨ B ⟩) i b)
            (Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) d)
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 d))
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d)))
              ∙ Dᴰ.reind-filler (λ i → transp (λ i₁ → D .fst) (~ i) (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d))))
              ∙ Dᴰ.reind-filler λ i → transp (λ i₁ → D .fst) i (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 (transp (λ i₁ → D .fst) i0 d))))
          ∙ C.reind-filler _
          ∙ C.reind-filler _
          ∙ C.reind-filler _
      where
      ⟨C⟩ : ⟨ A bp.× B ⟩ → Type _
      ⟨C⟩ ab = ⟨ C ab ⟩

      ⟨Dᴰ⟩ : ⟨ D ⟩ → Type _
      ⟨Dᴰ⟩ d = ⟨ Dᴰ d ⟩

      module C = hSetReasoning (A bp.× B) ⟨C⟩
      module Dᴰ = hSetReasoning D ⟨Dᴰ⟩

      cong₃fᴰ : ∀ {b b'} {d d'} {dᴰ dᴰ'} →
        (b≡b' : b ≡ b') →
        (dᴰ≡dᴰ' : (d , dᴰ) ≡ (d' , dᴰ')) →
        Path (Σ ⟨ A bp.× B ⟩ ⟨C⟩)
         ((f d , b) , fᴰ d  dᴰ b)
         ((f d' , b') , fᴰ d' dᴰ' b')
      cong₃fᴰ b≡b' dᴰ≡dᴰ' i =
        ((f (dᴰ≡dᴰ' i .fst)) , (b≡b' i)) ,
        (fᴰ (dᴰ≡dᴰ' i .fst) (dᴰ≡dᴰ' i .snd) (b≡b' i))


-- TODO
-- I think you need an extra assumption on F to make this construction work
--
-- We're given f : Δ → Γ
-- δ : Δ such that f δ ≡ π (fib .fst) with fib.fst : F Γ
-- and we need to construct some element in F Δ
--
-- In the product case, this is easy because the fst is δ and the snd is fib.fst.snd
-- but we cannot construct this abstractly. So I think in generality we may
-- only be able to build a concrete quantifier in SETᴰ when F is a limit or smth
-- module _
--   (F : Functor (SET ℓ) (SET ℓ))
--   (πF : NatTrans F Id)
--   {ℓ'}
--   where

--   private
--     module SET = Category (SET ℓ)
--     module SETᴰ = Fibers (SETᴰ ℓ (ℓ-max ℓ ℓ'))

--   open Functor
--   open UniversalElement
--   open UniversalElementⱽ

--   module _
--     (πF* : {Γ : SET.ob} → (Γᴰ : SETᴰ.ob[ Γ ]) →
--       CartesianLift (SETᴰ ℓ (ℓ-max ℓ ℓ')) Γᴰ (πF ⟦ Γ ⟧))
--     where

--     module _ {Γ : SET.ob} (Γᴰ : SETᴰ.ob[ F ⟅ Γ ⟆ ]) where
--       UniversalQuantifierFSETᴰ : UniversalQuantifierF F πF πF* Γᴰ
--       UniversalQuantifierFSETᴰ .vertexⱽ γ .fst =
--         ∀ (fib : fiber (πF ⟦ Γ ⟧) γ) → ⟨ Γᴰ (fib .fst) ⟩
--       UniversalQuantifierFSETᴰ .vertexⱽ γ .snd =
--         isSetΠ (λ fib → str (Γᴰ (fib .fst)))
--       UniversalQuantifierFSETᴰ .elementⱽ Fγ f =
--         subst (λ z → ⟨ Γᴰ z ⟩) (funExt⁻ (sym $ F .F-id) Fγ)
--           (πF* (UniversalQuantifierFSETᴰ .vertexⱽ) .elementⱽ Fγ f
--             (Fγ , refl))
--       UniversalQuantifierFSETᴰ .universalⱽ {y = Δ} {yᴰ = Δᴰ} {f = f} .fst fᴰ δ δᴰ fib =
--         {!!}
--         -- subst (λ z → ⟨ Γᴰ z ⟩) (fibf .snd) $
--         --   fᴰ (fibf .fst) δᴰ'
--         where
--         fibf : fiber (F ⟪ f ⟫) (fib .fst)
--         -- fibf .fst = F .F-hom (λ z → δ) (fib .fst)
--         fibf .fst = {!!}
--         fibf .snd = {!!}

--         δᴰ' : ⟨ (πF* Δᴰ .vertexⱽ) (fibf .fst) ⟩
--         δᴰ' = {!πF* Δᴰ .elementⱽ!}
--       UniversalQuantifierFSETᴰ .universalⱽ .snd = {!!}
