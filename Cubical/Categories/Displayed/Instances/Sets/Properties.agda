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
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

  isFibrationSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ : SETᴰ.ob[ X ]) →
    (Y : hSet ℓ) →
    (f : ⟨ Y ⟩ → ⟨ X ⟩) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') Y
      (reindPshᴰNatTrans (yoRec _ f) ((SETᴰ ℓ ℓ') [-][-, Xᴰ ]))
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .vertexⱽ y = Xᴰ (f y)
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .elementⱽ = λ _ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .fst =
    λ z → z
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .fst γᴰ =
     -- λ j → (transp
     --          (λ i → (x : fst Z) → fst (Zᴰ x) →
     --            fst (Xᴰ
     --              (hcomp
     --                (λ k → λ { (i = i0) → f (g x)
     --                         ; (i = i1) → f (g x)
     --                         ; (j = i1) → f (g x) })
     --                (hcomp
     --                  (λ k → λ { (~ i = i0) → f (g x)
     --                           ; (~ i = i1) → f (g x)
     --                           ; (j = i1) → f (g x) })
     --                  (f (g x))))))
     --          j (λ x p → γᴰ x p))
    funExt₂ λ z zᴰ →
      Xᴰ.Prectify  $
        Xᴰ.≡out $
          (sym $ Xᴰ.reind-filler _)
        ∙ Xᴰ.cong₂ᴰ γᴰ (sym $ Zᴰ.reind-filler _)
    where
    module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
    module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)
  isFibrationSETᴰueⱽ {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) .snd .snd γᴰ =
    funExt₂ λ _ _ →
      Xᴰ.Prectify $ Xᴰ.≡out $
      (sym $ Xᴰ.reind-filler _)
      ∙ (Xᴰ.cong₂ᴰ γᴰ $ sym $ Zᴰ.reind-filler _)
    where
    module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
    module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)

--   isFibrationSETᴰ : isFibration (SETᴰ ℓ ℓ')
--   isFibrationSETᴰ Xᴰ Y f = REPRⱽ (isFibrationSETᴰueⱽ Xᴰ Y f)

--   private
--     module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ ℓ') isFibrationSETᴰ

--   TerminalsⱽSETᴰueⱽ :
--     (X : hSet ℓ) →
--     UniversalElementⱽ' (SETᴰ ℓ ℓ') X UnitPshᴰ
--   TerminalsⱽSETᴰueⱽ X .vertexⱽ _ = Unit* , isSetUnit*
--   TerminalsⱽSETᴰueⱽ X .elementⱽ = tt
--   TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .fst _ _ _ = tt*
--   TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .fst = λ _ → refl
--   TerminalsⱽSETᴰueⱽ X .universalⱽ (A , Aᴰ , f) .snd .snd = λ _ → refl

--   TerminalsⱽSETᴰ : Terminalsⱽ (SETᴰ ℓ ℓ')
--   TerminalsⱽSETᴰ X = REPRⱽ (TerminalsⱽSETᴰueⱽ X)

--   BinProductsⱽSETᴰueⱽ :
--     {X : hSet ℓ} →
--     (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
--     UniversalElementⱽ' (SETᴰ ℓ ℓ') X ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
--   BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)
--   BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = (λ x z → z .fst) , (λ x z → z .snd)
--   BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ x .fst = λ z x₁ z₁ → z .fst x₁ z₁ , z .snd x₁ z₁
--   BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .fst (xᴰ , yᴰ) =
--     ΣPathP ((funExt₂ λ _ _ → Xᴰ.Prectify $ Xᴰ.≡out $
--                (sym $ Xᴰ.reind-filler _)
--                ∙ Xᴰ.cong₂ᴰ xᴰ (sym $ Zᴰ.reind-filler _)) ,
--             funExt₂ λ _ _ → Yᴰ.Prectify $ Yᴰ.≡out $
--                (sym $ Yᴰ.reind-filler _)
--                ∙ Yᴰ.cong₂ᴰ yᴰ (sym $ Zᴰ.reind-filler _))
--     where
--     module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
--     module Yᴰ = hSetReasoning X (λ y → ⟨ Yᴰ y ⟩)
--     module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)
--   BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd Zᴰ→XᴰYᴰ =
--     funExt₂ λ _ _ →
--       ΣPathP ((Xᴰ.Prectify $ Xᴰ.≡out $ (sym $ Xᴰ.reind-filler _)
--                ∙ Xᴰ.cong₂ᴰ (λ u v → Zᴰ→XᴰYᴰ u v .fst) (sym $ Zᴰ.reind-filler _)) ,
--               (Yᴰ.Prectify $ Yᴰ.≡out $ (sym $ Yᴰ.reind-filler _)
--               ∙ Yᴰ.cong₂ᴰ (λ u v → Zᴰ→XᴰYᴰ u v .snd) (sym $ Zᴰ.reind-filler _)))
--     where
--     module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
--     module Yᴰ = hSetReasoning X (λ y → ⟨ Yᴰ y ⟩)
--     module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)

--   BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
--   BinProductsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ)

--   open CartesianCategoryⱽ
--   SETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
--   SETᴰCCⱽ .Cᴰ = SETᴰ ℓ ℓ'
--   SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
--   SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
--   SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

--   -- AllLRⱽSETᴰueⱽ :
--   --   {X Y : hSet ℓ} →
--   --   (Xᴰ : SETᴰ.ob[ X ]) →
--   --   (Yᴰ : SETᴰ.ob[ Y ]) →
--   --   (f : ⟨ Y ⟩ → ⟨ X ⟩) →
--   --   UniversalElementⱽ' (SETᴰ ℓ ℓ') Y
--   --     ((SETᴰ ℓ ℓ' [-][-, Yᴰ ]) ×Psh reindPshᴰNatTrans (yoRec _ f) (SETᴰ ℓ ℓ' [-][-, Xᴰ ]))
--   -- AllLRⱽSETᴰueⱽ {Y = Y} Xᴰ Yᴰ f .vertexⱽ y .fst =
--   --   ⟨ Yᴰ y ⟩ × ⟨ (isFibrationSETᴰ._*_ {x = Y} f Xᴰ) y ⟩
--   -- AllLRⱽSETᴰueⱽ {Y = Y} Xᴰ Yᴰ f .vertexⱽ y .snd =
--   --   isSet× (Yᴰ y .snd) ((isFibrationSETᴰ._*_ {x = Y} f Xᴰ) y .snd)
--   -- AllLRⱽSETᴰueⱽ Xᴰ Yᴰ f .elementⱽ = (λ x z → z .fst) , (λ x z → z .snd)
--   -- AllLRⱽSETᴰueⱽ Xᴰ Yᴰ f .universalⱽ (Z , Zᴰ , _) .fst = λ z x z₁ → z .fst x z₁ , z .snd x z₁
--   -- AllLRⱽSETᴰueⱽ {X = X}{Y = Y} Xᴰ Yᴰ f .universalⱽ (Z , Zᴰ , _) .snd .fst (yᴰ , xᴰf) =
--   --   ΣPathP ((funExt₂ λ _ _ → Yᴰ.Prectify $ Yᴰ.≡out $
--   --              (sym $ Yᴰ.reind-filler _)
--   --              ∙ Yᴰ.cong₂ᴰ yᴰ (sym $ Zᴰ.reind-filler _)) ,
--   --           funExt₂ λ _ _ → Xᴰ.Prectify $ Xᴰ.≡out $
--   --              (sym $ Xᴰ.reind-filler _)
--   --              ∙ Xᴰ.cong₂ᴰ xᴰf (sym $ Zᴰ.reind-filler _))
--   --   where
--   --   module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
--   --   module Yᴰ = hSetReasoning Y (λ y → ⟨ Yᴰ y ⟩)
--   --   module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)
--   -- AllLRⱽSETᴰueⱽ {X = X}{Y = Y} Xᴰ Yᴰ f .universalⱽ (Z , Zᴰ , _) .snd .snd γᴰ =
--   --   funExt₂ λ _ _ →
--   --     ΣPathP ((Yᴰ.Prectify $ Yᴰ.≡out $ (sym $ Yᴰ.reind-filler _)
--   --              ∙ Yᴰ.cong₂ᴰ (λ u v → γᴰ u v .fst) (sym $ Zᴰ.reind-filler _)) ,
--   --             (Xᴰ.Prectify $ Xᴰ.≡out $ (sym $ Xᴰ.reind-filler _)
--   --             ∙ Xᴰ.cong₂ᴰ (λ u v → γᴰ u v .snd) (sym $ Zᴰ.reind-filler _)))
--   --   where
--   --   module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
--   --   module Yᴰ = hSetReasoning Y (λ y → ⟨ Yᴰ y ⟩)
--   --   module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)

--   AllLRⱽSETᴰ : AllLRⱽ (SETᴰ ℓ ℓ')
--   -- AllLRⱽSETᴰ Xᴰ Yᴰ f = REPRⱽ (AllLRⱽSETᴰueⱽ Xᴰ Yᴰ f)
--   AllLRⱽSETᴰ =
--     BinProductsⱽ+Fibration→AllLRⱽ (SETᴰ ℓ ℓ') BinProductsⱽSETᴰ isFibrationSETᴰ
-- --     ⟨ Bᴰ b ⟩ × ⟨ (isFibrationSETᴰ._*_ {x = B} f Aᴰ) b ⟩ ,
-- --     isSet× (Bᴰ b .snd) ((isFibrationSETᴰ._*_ {x = B} f Aᴰ) b .snd)
-- --   AllLRⱽSETᴰ {x = A} Aᴰ {x = B} Bᴰ f .snd =
-- --     Isos→PshIso
-- --       (λ (C , Cᴰ , g) →
-- --         iso (λ z → (λ x z₁ → z x z₁ .fst) , (λ x z₁ → z x z₁ .snd))
-- --             (λ z x z₁ → z .fst x z₁ , z .snd x z₁)
-- --             (λ _ → refl)
-- --             λ _ → refl)
-- --       (λ _ _ _ _ → ΣPathP (refl , funExt₂ λ _ _ →
-- --         Aᴰ.Prectify $ Aᴰ.≡out $
-- --           (sym $ Aᴰ.reind-filler _) ∙ Aᴰ.reind-filler _))
-- --       where
-- --       module Aᴰ = hSetReasoning A (λ a → ⟨ Aᴰ a ⟩)

--   -- ExponentialsⱽSETᴰueⱽ :
--   --   {X : hSet ℓ} →
--   --   (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
--   --   UniversalElementⱽ' (SETᴰ ℓ ℓ') X
--   --     (LRⱽObᴰ→LRⱽ (SETᴰ ℓ ℓ')
--   --       (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
--   -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)
--   -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = λ x z → z .fst (z .snd)
--   -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .fst = λ z x z₁ z₂ → z x (z₁ , z₂)
--   -- ExponentialsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , g) .snd .fst f =
--   --   funExt₂ λ z zᴰ → Yᴰ.Prectify $ Yᴰ.≡out $
--   --     (sym $ Yᴰ.reind-filler _)
--   --     ∙ {!!}
--   --   --   ∙ Yᴰ.cong₂ᴰ f
--   --   --       (×≡Snd-hSet (Z .snd)
--   --   --         ((sym $ Zᴰ.reind-filler _)
--   --   --         ∙ (sym $ Zᴰ.reind-filler _)
--   --   --         ∙ (sym $ Zᴰ.reind-filler _))
--   --   --         {!!})
--   --   where
--   --   module Xᴰ = hSetReasoning X (λ x → ⟨ Xᴰ x ⟩)
--   --   module Xᴰg = hSetReasoning Z (λ z → ⟨ Xᴰ (g z) ⟩)
--   --   module Yᴰ = hSetReasoning X (λ y → ⟨ Yᴰ y ⟩)
--   --   module Zᴰ = hSetReasoning Z (λ z → ⟨ Zᴰ z ⟩)
--   -- ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd = {!!}

--   -- ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
--   -- ExponentialsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ)


--   -- Exponentialsⱽ and UniversalQuantifiers are slow. Filling in the arguments below with "transp ..."
--   -- mitigates some of the performance issues, but only so much
--   ExponentialsⱽSETᴰ : Exponentialsⱽ (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
--   ExponentialsⱽSETᴰ {x = A} Aᴰ Bᴰ .fst a = (⟨ Aᴰ a ⟩ → ⟨ Bᴰ a ⟩) , isSet→ (Bᴰ a .snd)
--   ExponentialsⱽSETᴰ {x = A} Aᴰ Bᴰ .snd =
--     Isos→PshIso
--       (λ (C , Cᴰ , g) →
--         iso (λ z x z₁ → z x (z₁ .fst) (z₁ .snd))
--             (λ z x z₁ z₂ → z x (z₁ , z₂))
--             (λ _ → refl)
--             (λ _ → refl))
--       (λ C C' g p →
--         funExt₂ (λ u v →
--           {!!}))
--         -- Bᴰ.Prectify
--         --   {e' = λ i → C .snd .snd u}
--         --   $ Bᴰ.≡out $
--         --   (sym $ Bᴰ.reind-filler _)
--         --   ∙ Bᴰ.≡in {pth = refl}
--         --      (cong₃ p
--         --         (refl {x = g .fst (transp (λ j → fst (C .fst)) i0 u)})
--         --         (refl {x = g .snd .fst (transp (λ j → fst (C .fst)) i0 u)
--         --                      (transp (λ j → fst (C .snd .fst (transp (λ j₁ → fst (C .fst)) (~ j) u))) i0 (v .fst))})
--         --         (Aᴰ.Prectify
--         --           {e' = λ i → C' .snd .snd (g .fst (transp (λ j → fst (C .fst)) i0 u))}
--         --            $ Aᴰ.≡out $
--         --           (sym $ Aᴰ.reind-filler (λ i → g .snd .snd (~ i) (transp (λ j → fst (C .fst)) (~ i) u)))
--         --           ∙ Aᴰ.reind-filler (λ i → C .snd .snd (transp (λ j → fst (C .fst)) (~ i) u))
--         --           ∙ Aᴰ.reind-filler (λ i →
--         --                                C .snd .snd
--         --                                (transp (λ j → fst (C .fst)) (~ i)
--         --                                 (transp (λ j → fst (C .fst)) i0 u)))
--         --           ∙ Aᴰ.reind-filler (λ i →
--         --                                C .snd .snd
--         --                                (transp (λ j → fst (C .fst)) (~ i)
--         --                                 (transp (λ j → fst (C .fst)) i0
--         --                                  (transp (λ j → fst (C .fst)) i0 u))))
--         --           ∙ Aᴰ.reind-filler (λ i →
--         --                                C .snd .snd
--         --                                (transp (λ j → fst (C .fst)) i
--         --                                 (transp (λ j → fst (C .fst)) i0
--         --                                  (transp (λ j → fst (C .fst)) i0 u))))
--         --           ∙ Aᴰ.reind-filler _))
--           -- ∙ Bᴰ.reind-filler _))

--       where
--       module Aᴰ = hSetReasoning A (λ a → ⟨ Aᴰ a ⟩)
--       module Bᴰ = hSetReasoning A (λ a → ⟨ Bᴰ a ⟩)

-- -- -- module _ {ℓ} {ℓ'} where
-- -- --   private
-- -- --     module SET = Category (SET ℓ)
-- -- --     module SETᴰ = Fibers (SETᴰ ℓ (ℓ-max ℓ ℓ'))
-- -- --     bp = BinProductsSET {ℓSET = ℓ}
-- -- --     module bp = BinProductsNotation bp
-- -- --     module isFibrationSETᴰ = FibrationNotation (SETᴰ ℓ (ℓ-max ℓ ℓ')) isFibrationSETᴰ
-- -- --   module _ {A B : SET.ob} (Cᴰ : SETᴰ.ob[ A bp.× B ]) where
-- -- --     private
-- -- --       -×B = BinProducts→BinProductsWith (SET ℓ) B bp
-- -- --       module -×B = BinProductsWithNotation -×B

-- -- --     UniversalQuantifierSETᴰ :
-- -- --       UniversalQuantifier (SETᴰ ℓ (ℓ-max ℓ ℓ')) B -×B
-- -- --         (λ D Dᴰ → isFibrationSETᴰ Dᴰ -×B.×ue.vertex (-×B.π₁ {b = D}))
-- -- --         Cᴰ
-- -- --     UniversalQuantifierSETᴰ .fst a = (∀ (b : ⟨ B ⟩) → ⟨ Cᴰ (a , b) ⟩) , isSetΠ (λ _ → Cᴰ _ .snd)
-- -- --     UniversalQuantifierSETᴰ .snd =
-- -- --       Isos→PshIso
-- -- --         (λ _ → iso (λ z x₁ z₁ → z (fst x₁) z₁ (snd x₁))
-- -- --                    (λ z x₁ z₁ b → z (x₁ , b) z₁)
-- -- --                    (λ _ → refl)
-- -- --                    (λ _ → refl))
-- -- --         (λ C C' g p → funExt₂ λ u v →
-- -- --           let module C = hSetReasoning (C .fst) (λ c → ⟨ C .snd .fst c ⟩) in
-- -- --           let module C' = hSetReasoning (C' .fst) (λ c → ⟨ C' .snd .fst c ⟩) in
-- -- --           Cᴰ.Prectify
-- -- --             {e' = λ i → snd (C .snd) (fst u) , snd u}
-- -- --             $ Cᴰ.≡out $
-- -- --             (sym $ Cᴰ.reind-filler (λ i → g .snd .snd i (transp (λ j → fst (C .fst)) i (fst u)) , transp (λ j → fst B) i (snd u)))
-- -- --             ∙ (Cᴰ.≡in {pth = refl} $
-- -- --                   cong₃ p (refl {x = g .fst (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst))})
-- -- --                           (C'.Prectify {e' = λ i → g .fst (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- --                              C'.≡out $
-- -- --                               (C'.≡in {pth = λ i → g .fst (transportRefl (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst)) (~ i))} $
-- -- --                                 cong₂ (g .snd .fst)
-- -- --                                   (sym $ transportRefl (transp (λ _ → fst (C .fst)) i0 (u .fst)))
-- -- --                                   (C.Prectify {e' = λ i →
-- -- --                                                        transp (λ _ → fst (C .fst)) (~ i)
-- -- --                                                        (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- --                                      C.≡out $ (sym $ C.reind-filler _) ∙ C.reind-filler _ ∙ C.reind-filler _ ))
-- -- --                               ∙ C'.reind-filler _)
-- -- --                           (refl {x = transp (λ _ → ⟨ B ⟩) i0 (u .snd)}))
-- -- --             ∙ Cᴰ.reind-filler _
-- -- --         )
-- -- --         where
-- -- --         module Cᴰ = hSetReasoning (A bp.× B) (λ c → ⟨ Cᴰ c ⟩)

-- -- --   open CartesianClosedCategoryⱽ

-- -- --   SETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ ℓ'))) (ℓ-max ℓ (ℓ-max ℓ ℓ'))
-- -- --   SETᴰCCCⱽ .CCⱽ = SETᴰCCⱽ
-- -- --   SETᴰCCCⱽ .lrⱽ = AllLRⱽSETᴰ
-- -- --   SETᴰCCCⱽ .expⱽ = ExponentialsⱽSETᴰ
-- -- --   SETᴰCCCⱽ .forallⱽ = UniversalQuantifierSETᴰ
