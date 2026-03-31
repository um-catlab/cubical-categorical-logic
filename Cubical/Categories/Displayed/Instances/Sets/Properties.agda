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

open import Cubical.Categories.Instances.Fiber hiding (fiber)

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
open UniversalElementⱽ'-Equiv

module _ {ℓA ℓB : Level} {A : Type ℓA} {B : A → Type ℓB} where
  open depReasoning B using (isEquivReind; equivReind) public

module _ {ℓ ℓ'} where
  private
    module SET = Category (SET ℓ)
    module SETᴰ = Fibers (SETᴰ ℓ ℓ')

  isFibrationSETᴰueⱽ-Equiv :
    {X : hSet ℓ} →
    (Xᴰ : SETᴰ.ob[ X ]) →
    (Y : hSet ℓ) →
    (f : ⟨ Y ⟩ → ⟨ X ⟩) →
    UniversalElementⱽ'-Equiv (SETᴰ ℓ ℓ') Y
      (reindPshᴰNatTrans (yoRec ((SET ℓ) [-, X ]) f)
      ((SETᴰ ℓ ℓ') [-][-, Xᴰ ]))
  isFibrationSETᴰueⱽ-Equiv {X = X} Xᴰ Y f .vertexⱽ y = Xᴰ (f y)
  isFibrationSETᴰueⱽ-Equiv {X = X} Xᴰ Y f .elementⱽ = λ _ z → z
  isFibrationSETᴰueⱽ-Equiv {X = X} Xᴰ Y f .universalⱽ (Z , Zᴰ , g) =
    isEquivReind _

  isFibrationSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ : SETᴰ.ob[ X ]) →
    (Y : hSet ℓ) →
    (f : ⟨ Y ⟩ → ⟨ X ⟩) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') Y
      (reindPshᴰNatTrans (yoRec ((SET ℓ) [-, X ]) f)
      ((SETᴰ ℓ ℓ') [-][-, Xᴰ ]))
  isFibrationSETᴰueⱽ Xᴰ Y f =
    toUniversalElementⱽ' (isFibrationSETᴰueⱽ-Equiv Xᴰ Y f)

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

  -- Products using equivs
  -- This doesn't need to be opaque because
  -- equivReind can (and should) be transparent
  -- takes too long to rebuild so I'm not doing that rn
  --
  -- This is the minimal litmus test for usage of equivs for vertical univprops
  opaque
    unfolding equivReind
    BinProductsⱽSETᴰueⱽ-Equiv :
      {X : hSet ℓ} →
      (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
      UniversalElementⱽ'-Equiv (SETᴰ ℓ ℓ') X
        ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
    BinProductsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .vertexⱽ x =
      _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)
    BinProductsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .elementⱽ =
      (λ x z → z .fst) , (λ x z → z .snd)
    BinProductsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .universalⱽ (A , B , f) =
      -- I think reasoning chains like this could be made nicer
      -- currently I convert from an isEquiv obligation to an Equiv (≃) obligation
      -- This change in interface throws out some inference of the goals
      --
      -- This doesn't need to decompose into β + extensionality, it
      -- does both at once using equivalence reasoning principles
      equivIsEquiv $
        equivΠCod (λ _ → Σ-Π-≃)
        ∙ₑ Σ-Π-≃
        ∙ₑ ≃-× (equivReind {B = λ g → (z : ⟨ A ⟩) → ⟨ B z ⟩ → Xᴰ (g z) .fst} (SET.⋆IdR f))
                (equivReind {B = λ g → (z : ⟨ A ⟩) → ⟨ B z ⟩ → Yᴰ (g z) .fst} (SET.⋆IdR f))

  -- Using Isos
  BinProductsⱽSETᴰueⱽ :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ' (SETᴰ ℓ ℓ') X
      ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .vertexⱽ x = _ , isSet× (Xᴰ x .snd) (Yᴰ x .snd)
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .elementⱽ = (λ x z → z .fst) , (λ x z → z .snd)
  BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ x .fst = λ z x₁ z₁ → z .fst x₁ z₁ , z .snd x₁ z₁
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .fst (xᴰ , yᴰ) =
    ΣPathP ((SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) ,
            (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} $
               SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _))
  BinProductsⱽSETᴰueⱽ {X = X} Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd Zᴰ→XᴰYᴰ =
    funExt₂ λ z zᴰ →
      ΣPathP (
        funExt₂⁻ (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ}{e' = refl} $
                    SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Xᴰ} _) z zᴰ ,
        funExt₂⁻ (SETᴰ.rectifyOut {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ}{e' = refl} $
                    SETᴰ.reind-filler⁻ {a = Z}{b = X}{aᴰ = Zᴰ}{bᴰ = Yᴰ} _) z zᴰ)

--   BinProductsⱽSETᴰueⱽ :
--     {X : hSet ℓ} →
--     (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
--     UniversalElementⱽ' (SETᴰ ℓ ℓ') X
--       ((SETᴰ ℓ ℓ' [-][-, Xᴰ ]) ×Psh (SETᴰ ℓ ℓ' [-][-, Yᴰ ]))
--   BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ =
--     toUniversalElementⱽ' (BinProductsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ)

  BinProductsⱽSETᴰ : BinProductsⱽ (SETᴰ ℓ ℓ')
  BinProductsⱽSETᴰ Xᴰ Yᴰ = REPRⱽ (BinProductsⱽSETᴰueⱽ Xᴰ Yᴰ)

--   open CartesianCategoryⱽ
--   SETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
--   SETᴰCCⱽ .Cᴰ = SETᴰ ℓ ℓ'
--   SETᴰCCⱽ .termⱽ = TerminalsⱽSETᴰ
--   SETᴰCCⱽ .bpⱽ = BinProductsⱽSETᴰ
--   SETᴰCCⱽ .cartesianLifts = isFibrationSETᴰ

  AllLRⱽSETᴰ : AllLRⱽ (SETᴰ ℓ ℓ')
  AllLRⱽSETᴰ =
    BinProductsⱽ+Fibration→AllLRⱽ (SETᴰ ℓ ℓ')
      BinProductsⱽSETᴰ isFibrationSETᴰ

  -- Exponentials with equivalences
  ExponentialsⱽSETᴰueⱽ-Equiv :
    {X : hSet ℓ} →
    (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
    UniversalElementⱽ'-Equiv (SETᴰ ℓ ℓ') X
      (LRⱽObᴰ→LRⱽ(SETᴰ ℓ ℓ')
        (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall (SETᴰ ℓ ℓ' ⟨ X ⟩[-][-, Yᴰ ]))
  ExponentialsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .vertexⱽ x =
    (⟨ Xᴰ x ⟩ → ⟨ Yᴰ x ⟩) , isSet→ (Yᴰ x .snd)
  ExponentialsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .elementⱽ = λ x z → z .fst (z .snd)
  ExponentialsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , f) =
    -- The real test is to see if this can be defined at all
    -- Goal is 64 lines fully normalized (shown below)
    {!!}

    -- First attempt: Annoyingly this approach of using ≃ to give an isEquiv throws
    -- out all useful information for the goal, so it's not clear how to make
    -- progress when using equivReind
    -- equivIsEquiv $ equivReind {!!}

    -- Looking at the goal,
    -- I would hope to be able to invoke equivReind or isEquivReind a handful of times
    --
    -- The goal is nearly identical to the β proof for the iso approach shown below,
    -- except instead of showing that we have a composite that equals the identity,
    -- we have an obligation to show that the map is an equivalence.
    -- Perhaps these obligations are too similar to allow this approach to be
    -- meaningfully different than the other one
    --
    -- The goal
    --
    -- isEquiv
    -- (λ gᴰ →
    --    depReasoning.reind
    --    (λ section₁ →
    --       (x : fst Z) →
    --       Σ (Zᴰ x .fst) (λ _ → Xᴰ (f x) .fst) → fst (Yᴰ (section₁ x)))
    --    (λ i →
    --       hcomp
    --       (λ i₁ .o →
    --          transp (λ i₂ → Z .fst → X .fst) i₁
    --          (primPOr (~ i) i (λ ._ x → f x) (λ ._ → f) _))
    --       (transp (λ i₁ → Z .fst → X .fst) i0
    --        (hcomp
    --         (doubleComp-faces (λ _ x → f x)
    --          (λ i₁ →
    --             hcomp (doubleComp-faces (λ _ x → f x) (λ i₂ x → f x) i₁)
    --             (λ x → f x))
    --          i)
    --         (λ x → f x))))
    --    (λ x p →
    --       gᴰ x
    --       (depReasoning.reind
    --        (λ section₁ →
    --           (x₁ : fst Z) →
    --           Σ (Zᴰ x₁ .fst) (λ _ → Xᴰ (f x₁) .fst) → fst (Zᴰ (section₁ x₁)))
    --        (λ _ x₁ → x₁) (λ x₁ p₁ → p₁ .fst) x p)
    --       (isEquivReind
    --        (λ i →
    --           hcomp (doubleComp-faces (λ _ x₁ → f x₁) (λ i₁ x₁ → f x₁) i)
    --           (hcomp (doubleComp-faces (λ _ x₁ → f x₁) (λ _ x₁ → f x₁) (~ i))
    --            (λ x₁ → f x₁)))
    --        .equiv-proof
    --        (depReasoning.reind
    --         (λ section₁ →
    --            (x₁ : fst Z) →
    --            Σ (Zᴰ x₁ .fst) (λ _ → Xᴰ (f x₁) .fst) → fst (Xᴰ (section₁ x₁)))
    --         (λ i →
    --            hcomp
    --            (doubleComp-faces (λ _ x₁ → f x₁)
    --             (λ i₁ →
    --                hcomp (doubleComp-faces (λ _ x₁ → f x₁) (λ i₂ x₁ → f x₁) i₁)
    --                (λ x₁ → f x₁))
    --             (~ i))
    --            (λ x₁ → f x₁))
    --         (depReasoning.reind
    --          (λ section₁ →
    --             (x₁ : fst Z) →
    --             Σ (Zᴰ x₁ .fst) (λ _ → Xᴰ (f x₁) .fst) → fst (Xᴰ (section₁ x₁)))
    --          (λ i x₁ → f x₁)
    --          (depReasoning.reind
    --           (λ section₁ →
    --              (x₁ : fst Z) →
    --              Σ (Zᴰ x₁ .fst) (λ _ → Xᴰ (f x₁) .fst) → fst (Xᴰ (section₁ x₁)))
    --           (λ i →
    --              hcomp (doubleComp-faces (λ _ x₁ → f x₁) (λ i₁ x₁ → f x₁) i)
    --              (hcomp (doubleComp-faces (λ _ x₁ → f x₁) (λ _ x₁ → f x₁) (~ i))
    --               (λ x₁ → f x₁)))
    --           (λ x₁ p₁ →
    --              depReasoning.reind
    --              (λ section₁ →
    --                 (x₂ : fst Z) →
    --                 Σ (Zᴰ x₂ .fst) (λ _ → Xᴰ (f x₂) .fst) → fst (Xᴰ (f (section₁ x₂))))
    --              (λ _ x₂ → x₂) (λ x₂ p₂ → p₂ .snd) x₁ p₁))))
    --        .fst .fst x p)))

  -- Exponentials with isos
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
    -- SETᴰ.rectifyOut $
    --   SETᴰ.reind-filler⁻ _
    --   ∙ SETᴰ.congᴰ (λ (u : uTy) z zᴰ → f z (u z zᴰ))
    --       (funExt₂ λ z zᴰ →
    --         ΣPathP ((funExt₂⁻ (SETᴰ.rectifyOut $ SETᴰ.reind-filler⁻ _) z zᴰ) ,
    --                  funExt₂⁻ (SETᴰ.rectifyOut $
    --                    -- This is what's slow
    --                    -- Ideas for fixes
    --                    -- 1. fill in arguments
    --                    -- 2. Avoid the funExt's here by writing a helper for reasoning
    --                    --    about products in SETᴰ
    --                    -- 3. Try to refactor using formal reinds such that there is
    --                    --    at most one reind. That is, so we need not encounter
    --                    --    reind _ (reind _ (reind _ ...))
    --                    --
    --                    --    Hypothesis:
    --                    --      the slowness isn't actually from computing big paths,
    --                    --      rather its the unification of the implicit arguments
    --                    --      to each of these reind fillers. If this is true, then
    --                    --      we may mitigate the slowness here by removing nested
    --                    --      reindexings
    --                     SETᴰ.reind-filler⁻ _
    --                    ∙ SETᴰ.reind-filler⁻ _
    --                    ∙ SETᴰ.reind-filler⁻ _
    --                    ∙ SETᴰ.reind-filler⁻ _)
    --                    z zᴰ))
    --   where
    --   g*Xᴰ = isFibrationSETᴰ._*_ {x = Z} g Xᴰ
    --   uTy = (z : ⟨ Z ⟩) → (⟨ Zᴰ z ⟩ × ⟨ Xᴰ (g z) ⟩) → ⟨ Zᴰ z ⟩ × ⟨ g*Xᴰ z ⟩
  ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ .universalⱽ (Z , Zᴰ , _) .snd .snd = {!!}

--   ExponentialsⱽSETᴰueⱽ :
--     {X : hSet ℓ} →
--     (Xᴰ Yᴰ : SETᴰ.ob[ X ]) →
--     UniversalElementⱽ' (SETᴰ ℓ ℓ') X
--       (LRⱽObᴰ-Equiv→LRⱽ-Equiv (SETᴰ ℓ ℓ')
--         (Xᴰ , AllLRⱽSETᴰ Xᴰ) ⇒ⱽPshSmall-Equiv (SETᴰ ℓ ℓ' ⟨ X ⟩[-][-, Yᴰ ]))
--   ExponentialsⱽSETᴰueⱽ Xᴰ Yᴰ =
--     toUniversalElementⱽ' (ExponentialsⱽSETᴰueⱽ-Equiv Xᴰ Yᴰ)

--   ExponentialsⱽSETᴰ : Exponentialsⱽ-Equiv (SETᴰ ℓ ℓ') AllLRⱽSETᴰ
--   ExponentialsⱽSETᴰ = ExponentialsⱽSETᴰueⱽ-Equiv

-- -- -- -- -- -- --     UniversalQuantifierSETᴰ :
-- -- -- -- -- -- --       UniversalQuantifier (SETᴰ ℓ (ℓ-max ℓ ℓ')) B -×B
-- -- -- -- -- -- --         (λ D Dᴰ → isFibrationSETᴰ Dᴰ -×B.×ue.vertex (-×B.π₁ {b = D}))
-- -- -- -- -- -- --         Cᴰ
-- -- -- -- -- -- --     UniversalQuantifierSETᴰ .fst a = (∀ (b : ⟨ B ⟩) → ⟨ Cᴰ (a , b) ⟩) , isSetΠ (λ _ → Cᴰ _ .snd)
-- -- -- -- -- -- --     UniversalQuantifierSETᴰ .snd =
-- -- -- -- -- -- --       Isos→PshIso
-- -- -- -- -- -- --         (λ _ → iso (λ z x₁ z₁ → z (fst x₁) z₁ (snd x₁))
-- -- -- -- -- -- --                    (λ z x₁ z₁ b → z (x₁ , b) z₁)
-- -- -- -- -- -- --                    (λ _ → refl)
-- -- -- -- -- -- --                    (λ _ → refl))
-- -- -- -- -- -- --         (λ C C' g p → funExt₂ λ u v →
-- -- -- -- -- -- --           let module C = hSetReasoning (C .fst) (λ c → ⟨ C .snd .fst c ⟩) in
-- -- -- -- -- -- --           let module C' = hSetReasoning (C' .fst) (λ c → ⟨ C' .snd .fst c ⟩) in
-- -- -- -- -- -- --           Cᴰ.Prectify
-- -- -- -- -- -- --             {e' = λ i → snd (C .snd) (fst u) , snd u}
-- -- -- -- -- -- --             $ Cᴰ.≡out $
-- -- -- -- -- -- --             (sym $ Cᴰ.reind-filler (λ i → g .snd .snd i (transp (λ j → fst (C .fst)) i (fst u)) , transp (λ j → fst B) i (snd u)))
-- -- -- -- -- -- --             ∙ (Cᴰ.≡in {pth = refl} $
-- -- -- -- -- -- --                   cong₃ p (refl {x = g .fst (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst))})
-- -- -- -- -- -- --                           (C'.Prectify {e' = λ i → g .fst (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- -- -- -- -- --                              C'.≡out $
-- -- -- -- -- -- --                               (C'.≡in {pth = λ i → g .fst (transportRefl (transp (λ _ → ⟨ C .fst ⟩) i0 (u .fst)) (~ i))} $
-- -- -- -- -- -- --                                 cong₂ (g .snd .fst)
-- -- -- -- -- -- --                                   (sym $ transportRefl (transp (λ _ → fst (C .fst)) i0 (u .fst)))
-- -- -- -- -- -- --                                   (C.Prectify {e' = λ i →
-- -- -- -- -- -- --                                                        transp (λ _ → fst (C .fst)) (~ i)
-- -- -- -- -- -- --                                                        (transp (λ _ → fst (C .fst)) i0 (u .fst))} $
-- -- -- -- -- -- --                                      C.≡out $ (sym $ C.reind-filler _) ∙ C.reind-filler _ ∙ C.reind-filler _ ))
-- -- -- -- -- -- --                               ∙ C'.reind-filler _)
-- -- -- -- -- -- --                           (refl {x = transp (λ _ → ⟨ B ⟩) i0 (u .snd)}))
-- -- -- -- -- -- --             ∙ Cᴰ.reind-filler _
-- -- -- -- -- -- --         )
-- -- -- -- -- -- --         where
-- -- -- -- -- -- --         module Cᴰ = hSetReasoning (A bp.× B) (λ c → ⟨ Cᴰ c ⟩)

-- -- -- -- -- -- --   open CartesianClosedCategoryⱽ

-- -- -- -- -- -- --   SETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc (ℓ-max ℓ ℓ'))) (ℓ-max ℓ (ℓ-max ℓ ℓ'))
-- -- -- -- -- -- --   SETᴰCCCⱽ .CCⱽ = SETᴰCCⱽ
-- -- -- -- -- -- --   SETᴰCCCⱽ .lrⱽ = AllLRⱽSETᴰ
-- -- -- -- -- -- --   SETᴰCCCⱽ .expⱽ = ExponentialsⱽSETᴰ
-- -- -- -- -- -- --   SETᴰCCCⱽ .forallⱽ = UniversalQuantifierSETᴰ

-- -- import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Sets as EqSets
-- -- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
-- -- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianClosedV
-- -- open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.BiCartesianClosedV
-- -- open import Cubical.Categories.Displayed.Limits.BiCartesianClosedV

-- -- EqSETᴰCCⱽ : CartesianCategoryⱽ (SET ℓ) (ℓ-max ℓ (ℓ-suc ℓ')) (ℓ-max ℓ ℓ')
-- -- EqSETᴰCCⱽ = EqCCⱽ→CCⱽ EqSets.SetAssoc (SETᴰ _ _) EqSets.isCartesianⱽSETᴰ

-- -- EqSETᴰCCCⱽ : CartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
-- -- EqSETᴰCCCⱽ {ℓ = ℓ} =
-- --   EqCCCⱽ→CCCⱽ SETCC EqSets.SetAssoc EqSets.SetIdL EqSets.Setπ₁NatEq
-- --     EqSets.Set×aF-seq (SETᴰ ℓ ℓ) EqSets.isCCCⱽSETᴰ

-- -- EqSETᴰBCCCⱽ : BiCartesianClosedCategoryⱽ SETCC (ℓ-max ℓ (ℓ-suc ℓ)) (ℓ-max ℓ ℓ)
-- -- EqSETᴰBCCCⱽ {ℓ = ℓ} =
-- --   EqBCCCⱽ→BCCCⱽ SETCC EqSets.SetAssoc EqSets.SetIdL EqSets.Setπ₁NatEq
-- --     EqSets.Set×aF-seq (SETᴰ ℓ ℓ) EqSets.SetAssoc^op
-- --     EqSets.isCCCⱽSETᴰ EqSets.isCartesianⱽSETᴰ^op
