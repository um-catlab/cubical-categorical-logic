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
  hiding (_[-][-,_])
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.UniversalQuantifier
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.Exponential
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
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
open UniversalElementⱽ'

module _ {ℓ ℓ'} where
  private
    module SET = Category (SET ℓ)
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

  isFibrationSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ : SETᴰ.ob[ X ]) →
    (Y : hSet ℓ) →
    (f : ⟨ Y ⟩ → ⟨ X ⟩) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') Y
      (reindPshᴰNatTrans (yoRec ((SET ℓ) [-, X ]) f)
      ((SETᴰ ℓ ℓ') [-][-, Xᴰ ]))
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .vertexⱽ y = Xᴰ (f y)
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .elementⱽ = λ _ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .fst =
    λ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .fst γᴰ =
    -- I think these should have better inference for implicits if hSet were either
    -- 1. opaque, or
    -- 2. a no-eta-equality record
    --
    -- TODO make a local wrapper around hSet to test that
    SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
      SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .snd γᴰ =
    SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
      SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _

  isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
  isFibrationSETᴰ Xᴰ Y f = REPRⱽ (isFibrationSETᴰueⱽ Xᴰ Y f)

  private
    module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ ℓ') isFibrationSETᴰ

  TerminalsⱽSETᴰueⱽ :
    (X : hSet ℓ) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X UnitPshᴰ
  TerminalsⱽSETᴰueⱽ X .vertexⱽ _ = Unit* , isSetUnit*
  TerminalsⱽSETᴰueⱽ X .elementⱽ = tt
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .fst _ _ _ = tt*
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .fst = λ _ → refl
  TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .snd = λ _ → refl

  TerminalsⱽSETᴰ : Terminalsⱽ (SETᴰ ℓ ℓ')
  TerminalsⱽSETᴰ X = REPRⱽ (TerminalsⱽSETᴰueⱽ X)

  _×ⱽSETᴰ_ : {X : hSet ℓ} → (Xᴰ Yᴰ : SETᴰ.ob[ X ]) → SETᴰ.ob[ X ]
  Xᴰ ×ⱽSETᴰ Yᴰ = λ x → _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)

  SETᴰπ₁ⱽ :
    ∀ {X} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    SETᴰ.Hom[ (λ (x : ⟨ X ⟩) → x) ][ Xᴰ ×ⱽSETᴰ Yᴰ , Xᴰ ]
  SETᴰπ₁ⱽ Xᴰ Yᴰ = λ x z → z .fst

  SETᴰπ₂ⱽ :
    ∀ {X} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    SETᴰ.Hom[ (λ (x : ⟨ X ⟩) → x) ][ Xᴰ ×ⱽSETᴰ Yᴰ , Yᴰ ]
  SETᴰπ₂ⱽ Xᴰ Yᴰ = λ x z → z .snd

  opaque
    SETᴰ×ⱽHelper :
      ∀ {X Z} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      (Zᴰ : SETᴰ.ob[ Z ]) →
      {f : (SET ℓ) [ Z , X ]} →
      (fᴰ gᴰ : SETᴰ.Hom[ f ][ Zᴰ , Xᴰ ×ⱽSETᴰ Yᴰ ]) →
      SETᴰ._∫≡_ {b = X}{bᴰ = Xᴰ}
      (SETᴰ._⋆ᴰ_ {z = X}{g = λ x → x} fᴰ (SETᴰπ₁ⱽ Xᴰ Yᴰ))
      (SETᴰ._⋆ᴰ_ {z = X}{g = λ x → x} gᴰ (SETᴰπ₁ⱽ Xᴰ Yᴰ)) →
      SETᴰ._∫≡_ {b = X}{bᴰ = Yᴰ}
      (SETᴰ._⋆ᴰ_ {z = X}{g = λ x → x} fᴰ (SETᴰπ₂ⱽ Xᴰ Yᴰ))
      (SETᴰ._⋆ᴰ_ {z = X}{g = λ x → x} gᴰ (SETᴰπ₂ⱽ Xᴰ Yᴰ)) →
      fᴰ ≡ gᴰ
    SETᴰ×ⱽHelper Xᴰ Yᴰ Zᴰ fᴰ gᴰ fst≡ snd≡ =
      funExt₂ (λ z zᴰ →
        ΣPathP (funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} fst≡) z zᴰ ,
                funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} snd≡) z zᴰ))

  BinProductsⱽSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X
      ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ = Xᴰ ×ⱽSETᴰ Yᴰ
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = SETᴰπ₁ⱽ Xᴰ Yᴰ , SETᴰπ₂ⱽ Xᴰ Yᴰ
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ x .fst = λ z x₁ z₁ → z .fst x₁ z₁ , z .snd x₁ z₁
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .fst (xᴰ , yᴰ) =
    ΣPathP ((SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) ,
            (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ}{e' = SETᴰ.wrap refl} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _))
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd Zᴰ→XᴰYᴰ =
    SETᴰ×ⱽHelper Xᴰ Yᴰ Zᴰ _ Zᴰ→XᴰYᴰ (SETᴰ.reind-filler⁻ _) (SETᴰ.reind-filler⁻ _)

  BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
  BinProductsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ)

  open CartesianCategoryⱽ
  SETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰCCⱽ .Cᴰ = SETᴰ ℓ ℓ'
  SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
  SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
  SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

  AllLRⱽSETᴰ : AllLRⱽ (SETᴰ ℓ ℓ')
  AllLRⱽSETᴰ =
    BinProductsⱽ+Fibration→AllLRⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ

  -- NOTE: Here and below have not yet been fixed subject to making reind opaque
  -- The fixes to the first path in ExponentialsⱽSETᴰ are somewhat scaffolded but
  -- not complete.
  -- UniversalQuantifierSETᴰ hasn't been touched yet
  --
  ExponentialsⱽSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X
      (LRⱽObᴰ→LRⱽ (SETᴰ ℓ ℓ')
        (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall (SETᴰ ℓ ℓ' ⟨ X ⟩[-][-, Yᴰ ]))
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = λ x z → z .fst (z .snd)
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .fst = λ z x z₁ z₂ → z x (z₁ , z₂)
  ExponentialsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , g) .snd .fst f =
    {!!}
    -- SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $
    --   SETᴰ.reind-filler⁻ _
    --   ∙ SETᴰ.congᴰ (λ (u : uTy) z zᴰ → f z (u z zᴰ))
    --      (SETᴰ×ⱽHelper Zᴰ g*Xᴰ (Zᴰ ×ⱽSETᴰ g*Xᴰ) _ _ (SETᴰ.reind-filler⁻ _)
    --         {!!})
    --       -- (funExt₂ λ z zᴰ →
    --       --   ΣPathP ((funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $ SETᴰ.reind-filler⁻ _) z zᴰ) ,
    --       --            funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $
    --       --               SETᴰ.reind-filler⁻ _
    --       --              ∙ SETᴰ.reind-filler⁻ _
    --       --              ∙ SETᴰ.reind-filler⁻ (SETᴰ.wrap {!refl!})
    --       --              ∙ SETᴰ.reind-filler⁻ (SETᴰ.wrap refl))
    --       --              z zᴰ))
    --   where
    --   g*Xᴰ = isFibrationSETᴰ._*_ {x = Z} g Xᴰ
    --   uTy = (z : ⟨ Z ⟩) → (⟨ Zᴰ z ⟩ × ⟨ Xᴰ (g z) ⟩) → ⟨ Zᴰ z ⟩ × ⟨ g*Xᴰ z ⟩
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd = {!!}

--   -- ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
--   -- ExponentialsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ)

-- -- -- -- -- --     UniversalQuantifierSETᴰ :
-- -- -- -- -- --       UniversalQuantifier (SETᴰ ℓ (ℓ-max ℓ ℓ')) B -×B
-- -- -- -- -- --         (λ D Dᴰ → isFibrationSETᴰ Dᴰ -×B.×ue.vertex (-×B.π₁ {b = D}))
-- -- -- -- -- --         Cᴰ
-- -- -- -- -- --     UniversalQuantifierSETᴰ .fst a = (∀ (b : ⟨ B ⟩) → ⟨ Cᴰ (a , b) ⟩) , isSetΠ (λ _ → Cᴰ _ .snd)
-- -- -- -- -- --     UniversalQuantifierSETᴰ .snd =
-- -- -- -- -- --       Isos→PshIso
-- -- -- -- -- --         (λ _ → iso (λ z x₁ z₁ → z (fst x₁) z₁ (snd x₁))
-- -- -- -- -- --                    (λ z x₁ z₁ b → z (x₁ , b) z₁)
-- -- -- -- -- --                    (λ _ → refl)
-- -- -- -- -- --                    (λ _ → refl))
-- -- -- -- -- --         (λ C C' g p → funExt₂ λ u v →
-- -- -- -- -- --           let module C = hSetReasoning (C .fst) (λ c → ⟨ C .snd .fst c ⟩) in
-- -- -- -- -- --           let module C' = hSetReasoning (C' .fst) (λ c → ⟨ C' .snd .fst c ⟩) in
-- -- -- -- -- --           Cᴰ.Prectify
-- -- -- -- -- --             {e' = λ i → snd (C .snd) (fst u) , snd u}
-- -- -- -- -- --             $ Cᴰ.≡out $
-- -- -- -- -- --             (sym $ Cᴰ.reind-filler (λ i → g .snd .snd i (transp (λ j → fst (C .fst)) i (fst u)) , transp (λ j → fst B) i (snd u)))
-- -- -- -- -- --             ∙ (Cᴰ.≡in {pth = refl} $
-- -- -- -- -- --                   cong₃ p (refl {x = g .fst (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst))})
-- -- -- -- -- --                           (C'.Prectify {e' = λ i → g .fst (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- -- -- -- --                              C'.≡out $
-- -- -- -- -- --                               (C'.≡in {pth = λ i → g .fst (transportRefl (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst)) (~ i))} $
-- -- -- -- -- --                                 cong₂ (g .snd .fst)
-- -- -- -- -- --                                   (sym $ transportRefl (transp (λ _ → fst (C .fst)) i0 (u .fst)))
-- -- -- -- -- --                                   (C.Prectify {e' = λ i →
-- -- -- -- -- --                                                        transp (λ _ → fst (C .fst)) (~ i)
-- -- -- -- -- --                                                        (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- -- -- -- --                                      C.≡out $ (sym $ C.reind-filler _) ∙ C.reind-filler _ ∙ C.reind-filler _ ))
-- -- -- -- -- --                               ∙ C'.reind-filler _)
-- -- -- -- -- --                           (refl {x = transp (λ _ → ⟨ B ⟩) i0 (u .snd)}))
-- -- -- -- -- --             ∙ Cᴰ.reind-filler _
-- -- -- -- -- --         )
-- -- -- -- -- --         where
-- -- -- -- -- --         module Cᴰ = hSetReasoning (A bp.× B) (λ c → ⟨ Cᴰ c ⟩)

-- -- -- -- -- --   open CartesianClosedCategoryⱽ

-- -- -- -- -- --   SETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ ℓ'))) (ℓ-max ℓ (ℓ-max ℓ ℓ'))
-- -- -- -- -- --   SETᴰCCCⱽ .CCⱽ = SETᴰCCⱽ
-- -- -- -- -- --   SETᴰCCCⱽ .lrⱽ = AllLRⱽSETᴰ
-- -- -- -- -- --   SETᴰCCCⱽ .expⱽ = ExponentialsⱽSETᴰ
-- -- -- -- -- --   SETᴰCCCⱽ .forallⱽ = UniversalQuantifierSETᴰ
