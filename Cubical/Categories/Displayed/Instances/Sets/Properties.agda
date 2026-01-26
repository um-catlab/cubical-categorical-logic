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
    opaque
      SET' : Category (ℓ-suc ℓ) ℓ
      SET' = SET ℓ

      SETᴰ' : Categoryᴰ SET' (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
      SETᴰ' = SETᴰ ℓ ℓ'
    module SET = Category SET'
    module SETᴰ = Fibers SETᴰ'

  opaque
    unfolding SET' SETᴰ'
    isFibrationSETᴰueⱽ :
      {X Y : SET.ob} →
      (Xᴰ : SETᴰ.ob[ X ]) →
      (f : SET.Hom[ Y , X ]) →
      UniversalElementⱽ' SETᴰ' Y
        (reindPshᴰNatTrans (yoRec (SET' [-, X ]) f) (SETᴰ' [-][-, Xᴰ ]))
    isFibrationSETᴰueⱽ {X = X} Xᴰ f .vertexⱽ y = Xᴰ (f y)
    isFibrationSETᴰueⱽ {X = X} Xᴰ f .elementⱽ = λ _ z → z
    isFibrationSETᴰueⱽ {X = X} Xᴰ  f .universalⱽ (Z , Zᴰ , g) .fst =
      λ z → z
    isFibrationSETᴰueⱽ {X = X} Xᴰ f .universalⱽ (Z , Zᴰ , g) .snd .fst γᴰ =
      SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
        SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _
    isFibrationSETᴰueⱽ {X = X} Xᴰ f .universalⱽ (Z , Zᴰ , g) .snd .snd γᴰ =
      SETᴰ.rectifyOut {a = Z}{b = X} {aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
        SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _

  isFibrationSETᴰ : isFibration SETᴰ'
  isFibrationSETᴰ Xᴰ Y f = REPRⱽ (isFibrationSETᴰueⱽ Xᴰ f)

  private
    module isFibrationSETᴰ = FibrationNotation SETᴰ' isFibrationSETᴰ

  opaque
    unfolding SETᴰ'
    TerminalsⱽSETᴰueⱽ :
      (X : SET.ob) →
      UniversalElementⱽ' SETᴰ' X UnitPshᴰ
    TerminalsⱽSETᴰueⱽ X .vertexⱽ _ = Unit* , isSetUnit*
    TerminalsⱽSETᴰueⱽ X .elementⱽ = tt
    TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .fst _ _ _ = tt*
    TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .fst = λ _ → refl
    TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .snd = λ _ → refl

  TerminalsⱽSETᴰ : Terminalsⱽ SETᴰ'
  TerminalsⱽSETᴰ X = REPRⱽ (TerminalsⱽSETᴰueⱽ X)

  opaque
    unfolding SETᴰ'
    _×ⱽSETᴰ'_ : {X : SET.ob} → (Xᴰ Yᴰ : SETᴰ.ob[ X ]) → SETᴰ.ob[ X ]
    Xᴰ ×ⱽSETᴰ' Yᴰ = λ x → _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)

    SETᴰ'π₁ⱽ :
      ∀ {X} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      SETᴰ.Hom[ SET.id ][ Xᴰ ×ⱽSETᴰ' Yᴰ , Xᴰ ]
    SETᴰ'π₁ⱽ Xᴰ Yᴰ = λ x z → z .fst

    SETᴰ'π₂ⱽ :
      ∀ {X} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      SETᴰ.Hom[ SET.id ][ Xᴰ ×ⱽSETᴰ' Yᴰ , Yᴰ ]
    SETᴰ'π₂ⱽ Xᴰ Yᴰ = λ x z → z .snd

    SETᴰ×ⱽHelper :
      ∀ {X Z} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      (Zᴰ : SETᴰ.ob[ Z ]) →
      {f : SET.Hom[ Z , X ]} →
      (fᴰ gᴰ : SETᴰ.Hom[ f ][ Zᴰ , Xᴰ ×ⱽSETᴰ' Yᴰ ]) →
      SETᴰ._∫≡_ {b = X}{bᴰ = Xᴰ}
      (SETᴰ._⋆ᴰ_ {z = X}{g = SET.id} fᴰ (SETᴰ'π₁ⱽ Xᴰ Yᴰ))
      (SETᴰ._⋆ᴰ_ {z = X}{g = SET.id} gᴰ (SETᴰ'π₁ⱽ Xᴰ Yᴰ)) →
      SETᴰ._∫≡_ {b = X}{bᴰ = Yᴰ}
      (SETᴰ._⋆ᴰ_ {z = X}{g = SET.id} fᴰ (SETᴰ'π₂ⱽ Xᴰ Yᴰ))
      (SETᴰ._⋆ᴰ_ {z = X}{g = SET.id} gᴰ (SETᴰ'π₂ⱽ Xᴰ Yᴰ)) →
      fᴰ ≡ gᴰ
    SETᴰ×ⱽHelper Xᴰ Yᴰ Zᴰ fᴰ gᴰ fst≡ snd≡ =
      funExt₂ (λ z zᴰ →
        ΣPathP (funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} fst≡) z zᴰ ,
                funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} snd≡) z zᴰ))

    BinProductsⱽSETᴰueⱽ :
      {X : SET.ob} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      UniversalElementⱽ' SETᴰ' X
        ((SETᴰ' [-][-, Xᴰ ]) ×Psh (SETᴰ' [-][-, Yᴰ ]))
    BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ = Xᴰ ×ⱽSETᴰ' Yᴰ
    BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = SETᴰ'π₁ⱽ Xᴰ Yᴰ , SETᴰ'π₂ⱽ Xᴰ Yᴰ
    BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ x .fst = λ z x₁ z₁ → z .fst x₁ z₁ , z .snd x₁ z₁
    BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .fst (xᴰ , yᴰ) =
      ΣPathP ((SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = SETᴰ.wrap refl} $
                SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) ,
              (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ}{e' = SETᴰ.wrap refl} $
                SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _))
    BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd Zᴰ→XᴰYᴰ =
      SETᴰ×ⱽHelper Xᴰ Yᴰ Zᴰ _ Zᴰ→XᴰYᴰ (SETᴰ.reind-filler⁻ _) (SETᴰ.reind-filler⁻ _)

  BinProductsⱽSETᴰ : BinProductsⱽ SETᴰ'
  BinProductsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ)

  open CartesianCategoryⱽ
  SETᴰCCⱽ : CartesianCategoryⱽ SET' (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
  SETᴰCCⱽ .Cᴰ = SETᴰ'
  SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
  SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
  SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

  AllLRⱽSETᴰ : AllLRⱽ SETᴰ'
  AllLRⱽSETᴰ =
    BinProductsⱽ+Fibration→AllLRⱽ SETᴰ' BinProductsⱽSETᴰ isFibrationSETᴰ

  -- NOTE: Here and below have not yet been fixed subject to making reind opaque
  -- The fixes to the first path in ExponentialsⱽSETᴰ are somewhat scaffolded but
  -- not complete.
  -- UniversalQuantifierSETᴰ hasn't been touched yet
  --
  -- ExponentialsⱽSETᴰueⱽ :
  --   {X : hSet ℓ} →
  --   (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
  --   UniversalElementⱽ' (SETᴰ ℓ ℓ') X
  --     (LRⱽObᴰ→LRⱽ (SETᴰ ℓ ℓ')
  --       (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall (SETᴰ ℓ ℓ' ⟨ X ⟩[-][-, Yᴰ ]))
  -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)
  -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = λ x z → z .fst (z .snd)
  -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .fst = λ z x z₁ z₂ → z x (z₁ , z₂)
  -- ExponentialsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , g) .snd .fst f =
  --   SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $
  --     SETᴰ.reind-filler⁻ _
  --     ∙ {!!}

    --       -- (funExt₂ λ z zᴰ →
    --       --   ΣPathP ((funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $ SETᴰ.reind-filler⁻ _) z zᴰ) ,
    --       --            funExt₂⁻ (SETᴰ.rectifyOut {e' = SETᴰ.wrap refl} $
    --       --               SETᴰ.reind-filler⁻ _
    --       --              ∙ SETᴰ.reind-filler⁻ _
    --       --              ∙ SETᴰ.reind-filler⁻ (SETᴰ.wrap {!refl!})
    --       --              ∙ SETᴰ.reind-filler⁻ (SETᴰ.wrap refl))
    --       --              z zᴰ))
  --     where
  --     g*Xᴰ = isFibrationSETᴰ._*_ {x = Z} g Xᴰ
  --     uTy = (z : ⟨ Z ⟩) → (⟨ Zᴰ z ⟩ × ⟨ Xᴰ (g z) ⟩) → ⟨ Zᴰ z ⟩ × ⟨ g*Xᴰ z ⟩
  -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd = {!!}

  opaque
    unfolding SETᴰ'
    _⇒ⱽSETᴰ_ : {X : SET.ob} → (Xᴰ Yᴰ : SETᴰ.ob[ X ]) → SETᴰ.ob[ X ]
    Xᴰ ⇒ⱽSETᴰ Yᴰ = λ x → (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)

  module _ {X : SET.ob} (Xᴰ Yᴰ : SETᴰ.ob[ X ]) where
    opaque
      unfolding SETᴰ' BinProductsⱽSETᴰueⱽ _⇒ⱽSETᴰ_ isFibrationSETᴰueⱽ
      ExponentialsⱽSETᴰPointwiseIso :
        -- TODO make args explicit
        PshIsoPointwise
          {P = SETᴰ' [-][-, Xᴰ ⇒ⱽSETᴰ Yᴰ ]}
          {Q = LRⱽObᴰ→LRⱽ SETᴰ' (Xᴰ , AllLRⱽSETᴰ Xᴰ)
              ⇒ⱽPshSmall (SETᴰ' [-][-, Yᴰ ])}
      ExponentialsⱽSETᴰPointwiseIso (Z , Zᴰ , g) .Iso.fun = λ z x z₁ → z x (z₁ .fst) (z₁ .snd)
      ExponentialsⱽSETᴰPointwiseIso (Z , Zᴰ , g) .Iso.inv = λ z x z₁ z₂ → z x (z₁ , z₂)
      ExponentialsⱽSETᴰPointwiseIso (Z , Zᴰ , g) .Iso.sec = λ _ → refl
      ExponentialsⱽSETᴰPointwiseIso (Z , Zᴰ , g) .Iso.ret = λ _ → refl

      ExponentialsⱽSETᴰNatural : PshIsoNaturalTy ExponentialsⱽSETᴰPointwiseIso
      ExponentialsⱽSETᴰNatural x y f fᴰ =
        {!!}

  ExponentialsⱽSETᴰ : Exponentialsⱽ SETᴰ' AllLRⱽSETᴰ
  ExponentialsⱽSETᴰ Xᴰ Yᴰ .fst = Xᴰ ⇒ⱽSETᴰ Yᴰ
  ExponentialsⱽSETᴰ Xᴰ Yᴰ .snd =
    Isos→PshIso
      (ExponentialsⱽSETᴰPointwiseIso Xᴰ Yᴰ)
      (ExponentialsⱽSETᴰNatural Xᴰ Yᴰ)
      -- (λ _ _ _ _ →
      --   SETᴰ.rectifyOut $
      --     SETᴰ.congᴰ (Iso.fun (ExponentialsⱽSETᴰPointwiseIso Xᴰ Yᴰ _))
      --       (SETᴰ.rectifyOut $ SETᴰ.reind-filler⁻ _)
      --     ∙ {!!}
      --     ∙ {!!}
      --     ∙ SETᴰ.reind-filler _
      -- )

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
