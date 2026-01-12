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
open import Cubical.Categories.Displayed.Instances.Sets.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level
    ℓC ℓC' ℓD ℓD' : Level

open Categoryᴰ
open Category
open isIsoOver
open PshIso
open PshHom

module _ {ℓ ℓ'} where
  private
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')
  isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
  isFibrationSETᴰ {x = X} Xᴰ Y f .fst = λ z → Xᴰ (f z)
  isFibrationSETᴰ {x = X} Xᴰ Y f .snd =
    Isos→PshIso
      (λ _ → idIso)
      (λ _ _ _ _ →
        funExt₂ (λ _ _ →
        Xᴰ.Prectify $ Xᴰ.≡out $
          (sym $ Xᴰ.reind-filler _) ∙ Xᴰ.reind-filler _))
      where
      module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)

  private
    module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ ℓ') isFibrationSETᴰ

  TerminalsⱽSETᴰ : Terminalsⱽ (SETᴰ ℓ ℓ')
  TerminalsⱽSETᴰ X .fst _ = Unit* , isSetUnit*
  TerminalsⱽSETᴰ X .snd .trans = UnitPsh-intro
  TerminalsⱽSETᴰ X .snd .nIso _ .fst = λ _ _ _ → tt*
  TerminalsⱽSETᴰ X .snd .nIso _ .snd .fst = λ _ → refl
  TerminalsⱽSETᴰ X .snd .nIso _ .snd .snd = λ _ → refl

  open CartesianCategoryⱽ

  BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
  BinProductsⱽSETᴰ {x = A} Aᴰ Bᴰ .fst a =
    (⟨ Aᴰ a ⟩ × ⟨ Bᴰ a ⟩) , (isSet× (Aᴰ a .snd) (Bᴰ a .snd))
  BinProductsⱽSETᴰ {x = A} Aᴰ Bᴰ .snd =
    Isos→PshIso
      (λ (C , Cᴰ , f) →
        iso (λ z → (λ x z₁ → z x z₁ .fst) , (λ x z₁ → z x z₁ .snd))
            (λ z x z₁ → z .fst x z₁ , z .snd x z₁)
            (λ _ → refl)
            (λ _ → refl))
        (λ _ _ _ _ → ΣPathP (refl , refl))

  SETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰCCⱽ .Cᴰ = SETᴰ ℓ ℓ'
  SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
  SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
  SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

  AllLRⱽSETᴰ : AllLRⱽ (SETᴰ ℓ ℓ')
  AllLRⱽSETᴰ {x = A} Aᴰ {x = B} Bᴰ f .fst b =
    ⟨ Bᴰ b ⟩ × ⟨ (isFibrationSETᴰ._*_ {x = B} f Aᴰ) b ⟩ ,
    isSet× (Bᴰ b .snd) ((isFibrationSETᴰ._*_ {x = B} f Aᴰ) b .snd)
  AllLRⱽSETᴰ {x = A} Aᴰ {x = B} Bᴰ f .snd =
    Isos→PshIso
      (λ (C , Cᴰ , g) →
        iso (λ z → (λ x z₁ → z x z₁ .fst) , (λ x z₁ → z x z₁ .snd))
            (λ z x z₁ → z .fst x z₁ , z .snd x z₁)
            (λ _ → refl)
            λ _ → refl)
      (λ _ _ _ _ → ΣPathP (refl , funExt₂ λ _ _ →
        Aᴰ.Prectify $ Aᴰ.≡out $
          (sym $ Aᴰ.reind-filler _) ∙ Aᴰ.reind-filler _))
      where
      module Aᴰ = hSetReasoning A (λ a → ⟨ Aᴰ a ⟩)

  ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
  ExponentialsⱽSETᴰ {x = A} Aᴰ Bᴰ .fst a = (⟨ Aᴰ a ⟩ → ⟨ Bᴰ a ⟩) , isSet→ (Bᴰ a .snd)
  ExponentialsⱽSETᴰ {x = A} Aᴰ Bᴰ .snd =
    Isos→PshIso
      (λ (C , Cᴰ , g) →
        iso (λ z x z₁ → z x (z₁ .fst) (z₁ .snd))
            (λ z x z₁ z₂ → z x (z₁ , z₂))
            (λ _ → refl)
            (λ _ → refl))
      (λ C C' g p →
        funExt₂ (λ u v →
        Bᴰ.Prectify $ Bᴰ.≡out $
          (sym $ Bᴰ.reind-filler λ i → g .snd .snd i (transp (λ j → fst (C .fst)) i u))
          ∙ Bᴰ.≡in
             {pth = refl}
             (Bᴰ.Prectify $
              cong (λ z → p (g .fst (transp (λ j → ⟨ C .fst ⟩) i0 u))
                            (g .snd .fst (transp (λ j → ⟨ C .fst ⟩) i0 u)
                                         (transp (λ j → ⟨ C .snd .fst (transp (λ _ → ⟨ C .fst ⟩) (~ j) u) ⟩) i0 (v .fst)))
                            z)
                (Aᴰ.Prectify $ Aᴰ.≡out $
                  (sym $ Aᴰ.reind-filler λ i → g .snd .snd (~ i) (transp (λ j → fst (C .fst)) (~ i) u))
                  ∙ Aᴰ.reind-filler (λ i → C .snd .snd (transp (λ j → fst (C .fst)) (~ i) u))
                  ∙ Aᴰ.reind-filler (λ i →
                                       C .snd .snd
                                       (transp (λ j → fst (C .fst)) (~ i)
                                        (transp (λ j → fst (C .fst)) i0 u)))
                  ∙ Aᴰ.reind-filler (λ i →
                                       C .snd .snd
                                       (transp (λ j → fst (C .fst)) (~ i)
                                        (transp (λ j → fst (C .fst)) i0
                                         (transp (λ j → fst (C .fst)) i0 u))))
                  ∙ Aᴰ.reind-filler (λ i →
                                       C .snd .snd
                                       (transp (λ j → fst (C .fst)) i
                                        (transp (λ j → fst (C .fst)) i0
                                         (transp (λ j → fst (C .fst)) i0 u))))
                  ∙ Aᴰ.reind-filler _))
          ∙ Bᴰ.reind-filler _)
          )
      where
      module Aᴰ = hSetReasoning A (λ a → ⟨ Aᴰ a ⟩)
      module Bᴰ = hSetReasoning A (λ a → ⟨ Bᴰ a ⟩)


module _ {ℓ} {ℓ'} where
  private
    module SET = Category (SET ℓ)
    module SETᴰ = Fibers (SETᴰ ℓ (ℓ-max ℓ ℓ'))
    bp = BinProductsSET {ℓSET = ℓ}
    module bp = BinProductsNotation bp
    module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ (ℓ-max ℓ ℓ')) isFibrationSETᴰ
  module _ {A B : SET.ob} (Cᴰ : SETᴰ.ob[ A bp.× B ]) where
    private
      -×B = BinProducts→BinProductsWith (SET ℓ) B bp
      module -×B = BinProductsWithNotation -×B

    UniversalQuantifierSETᴰ :
      UniversalQuantifier (SETᴰ ℓ (ℓ-max ℓ ℓ')) B -×B
        (λ D Dᴰ → isFibrationSETᴰ Dᴰ -×B.×ue.vertex (-×B.π₁ {b = D}))
        Cᴰ
    UniversalQuantifierSETᴰ .fst a = (∀ (b : ⟨ B ⟩) → ⟨ Cᴰ (a , b) ⟩) , isSetΠ (λ _ → Cᴰ _ .snd)
    UniversalQuantifierSETᴰ .snd =
      Isos→PshIso
        (λ _ → iso (λ z x₁ z₁ → z (fst x₁) z₁ (snd x₁))
                   (λ z x₁ z₁ b → z (x₁ , b) z₁)
                   (λ _ → refl)
                   (λ _ → refl))
        (λ C C' g p → funExt₂ λ u v →
          let module C' = hSetReasoning (C' .fst) (λ c → ⟨ C' .snd .fst c ⟩) in
          Cᴰ.Prectify $ Cᴰ.≡out $
            (sym $ Cᴰ.reind-filler (λ i → g .snd .snd i (transp (λ j → fst (C .fst)) i (fst u)) , transp (λ j → fst B) i (snd u)))
            ∙ (Cᴰ.≡in {pth = refl} $ Cᴰ.Prectify $
                 cong (λ z → p (g .fst (transp (λ j → C .fst .fst) i0 (u .fst))) z (transp (λ _ → ⟨ B ⟩) i0 (u .snd)))
                   (C'.Prectify $ C'.≡out $
                     (C'.≡in {pth = λ i → g .fst (transportRefl (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst)) (~ i))} $
                       C'.Prectify $
                       cong₂ (g .snd .fst)
                         (sym $ transportRefl _)
                         (transport-filler (λ i →
                                              ⟨
                                              C .snd .fst
                                              (transportRefl (transp (λ j → ⟨ C .fst ⟩) (i0 ∨ i0) (fst u)) (~ i))
                                              ⟩) (transp
                                                  (λ j →
                                                     ⟨ C .snd .fst (transp (λ j₁ → ⟨ C .fst ⟩) (i0 ∨ i0 ∨ ~ j) (fst u))
                                                     ⟩)
                                                  (i0 ∨ i0) v)))
                     ∙ C'.reind-filler _))
            ∙ Cᴰ.reind-filler _
        )
        where
        module Cᴰ = hSetReasoning (A bp.× B) (λ c → ⟨ Cᴰ c ⟩)

  open CartesianClosedCategoryⱽ

  SETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ ℓ'))) (ℓ-max ℓ (ℓ-max ℓ ℓ'))
  SETᴰCCCⱽ .CCⱽ = SETᴰCCⱽ
  SETᴰCCCⱽ .lrⱽ = AllLRⱽSETᴰ
  SETᴰCCCⱽ .expⱽ = ExponentialsⱽSETᴰ
  SETᴰCCCⱽ .forallⱽ = UniversalQuantifierSETᴰ
