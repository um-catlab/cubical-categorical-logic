-- Parameterized unary CBPV syntax with finite value (co)products and
-- finite computation products.
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Prop

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝒱; r to 𝒞; ≤Vertex to ≤Kind)
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.CBPV.Unary.Base
open import Cubical.Categories.Displayed.CBPV.Unary.Additive

private
  variable
    ℓ ℓ' : Level

open Category
open Categoryᴰ
open UniversalElement

module CBPV (BaseTy : Kind → Type ℓ) where
  data Ob : Kind → Type ℓ where
    gen : ∀ {k} → BaseTy k → Ob k
    [F] : Ob 𝒱 → Ob 𝒞
    [U] : Ob 𝒞 → Ob 𝒱
    [1] [0] : Ob 𝒱
    _[×]_ _[+]_ : Ob 𝒱 → Ob 𝒱 → Ob 𝒱
    [⊤] : Ob 𝒞
    _[&]_ : Ob 𝒞 → Ob 𝒞 → Ob 𝒞

  VTy = Ob 𝒱
  CTy = Ob 𝒞

  module Terms (Fun : ∀ {k₁ k₂} → ≤Kind k₁ k₂ → Ob k₁ → Ob k₂ → Type ℓ') where
    private
      variable
        k k₁ k₂ : Kind
        Γ Δ Θ Ξ : Ob k
        A A₁ A₂ : VTy
        B B₁ B₂ : CTy
        k≤ k≤' k≤'' : ≤Kind k₁ k₂

    data Tm : (p : ≤Kind k₁ k₂) → Ob k₁ → Ob k₂ → Type (ℓ-max ℓ ℓ') where
      gen : Fun k≤ Γ Δ → Tm k≤ Γ Δ
      idS : Tm (≤V-refl k) Γ Γ
      seqS : Tm k≤ Γ Δ → Tm k≤' Δ Θ → Tm (≤V-trans k≤ k≤') Γ Θ
      IdLS : (f : Tm k≤ Γ Δ) → seqS idS f ≡ f
      IdRS : (f : Tm k≤ Γ Δ) → seqS f idS ≡ f
      AssocS : (f : Tm k≤ Γ Δ) (g : Tm k≤' Δ Θ)
        (h : Tm k≤'' Θ Ξ) → seqS (seqS f g) h ≡ seqS f (seqS g h)
      isSetTm : isSet (Tm k≤ Γ Δ)

      -- Multiplicative sturcture
      [ret] : Tm _ A ([F] A)
      [bind] : Tm _ A B → Tm _ ([F] A) B
      [Fβ] : (M : Tm _ A B) → seqS [ret] ([bind] M) ≡ M
      [Fη] : (K : Tm _ ([F] A) B) → K ≡ [bind] (seqS [ret] K)
      [force] : Tm _ ([U] B) B
      [thunk] : Tm _ Γ B → Tm {k₁ = 𝒱} _ Γ ([U] B)
      [Uβ] : (M : Tm _ A B) → seqS ([thunk] M) [force] ≡ M
      [Uη] : (V : Tm _ Γ ([U] B)) → V ≡ [thunk] (seqS V [force])

      -- Additive sturcture

      -- value products
      [1I] : Tm _ A [1]
      [1η] : (V : Tm _ A [1]) → V ≡ [1I]
      [×I] : Tm _ A A₁ → Tm _ A A₂ → Tm _ A (A₁ [×] A₂)
      [×π1] : Tm _ (A₁ [×] A₂) A₁
      [×π2] : Tm _ (A₁ [×] A₂) A₂
      [×β1] : (V₁ : Tm _ A A₁) (V₂ : Tm _ A A₂) → seqS ([×I] V₁ V₂) [×π1] ≡ V₁
      [×β2] : (V₁ : Tm _ A A₁) (V₂ : Tm _ A A₂) → seqS ([×I] V₁ V₂) [×π2] ≡ V₂
      [×η] : (V : Tm _ A (A₁ [×] A₂)) →
        V ≡ [×I] (seqS V [×π1]) (seqS V [×π2])

      -- value coproducts
      [0E] : Tm {k₁ = 𝒱} k≤ [0] Γ
      [0η] : (V : Tm {k₁ = 𝒱} k≤ [0] Γ) → V ≡ [0E]
      [+I1] : Tm _ A₁ (A₁ [+] A₂)
      [+I2] : Tm _ A₂ (A₁ [+] A₂)
      [+E] : Tm {k₁ = 𝒱} k≤ A₁ Γ → Tm {k₁ = 𝒱} k≤ A₂ Γ →
        Tm {k₁ = 𝒱} k≤ (A₁ [+] A₂) Γ
      [+β1] : (f : Tm {k₁ = 𝒱} k≤ A₁ Γ) (g : Tm {k₁ = 𝒱} k≤ A₂ Γ) →
        seqS [+I1] ([+E] f g) ≡ f
      [+β2] : (f : Tm {k₁ = 𝒱} k≤ A₁ Γ) (g : Tm {k₁ = 𝒱} k≤ A₂ Γ) →
        seqS [+I2] ([+E] f g) ≡ g
      [+η] : (f : Tm {k₁ = 𝒱} k≤ (A₁ [+] A₂) Γ) →
        f ≡ [+E] (seqS [+I1] f) (seqS [+I2] f)

      -- computation products
      [⊤I] : Tm (≤V-r-⊤ k) Γ [⊤]
      [⊤η] : (M : Tm (≤V-r-⊤ k) Γ [⊤]) → M ≡ [⊤I]
      [&I] : Tm (≤V-r-⊤ k) Γ B₁ → Tm (≤V-r-⊤ k) Γ B₂ →
        Tm (≤V-r-⊤ k) Γ (B₁ [&] B₂)
      [&π1] : Tm _ (B₁ [&] B₂) B₁
      [&π2] : Tm _ (B₁ [&] B₂) B₂
      [&β1] : (M₁ : Tm (≤V-r-⊤ k) Γ B₁) (M₂ : Tm (≤V-r-⊤ k) Γ B₂) →
        seqS ([&I] M₁ M₂) [&π1] ≡ M₁
      [&β2] : (M₁ : Tm (≤V-r-⊤ k) Γ B₁) (M₂ : Tm (≤V-r-⊤ k) Γ B₂) →
        seqS ([&I] M₁ M₂) [&π2] ≡ M₂
      [&η] : (M : Tm (≤V-r-⊤ k) Γ (B₁ [&] B₂)) →
        M ≡ [&I] (seqS M [&π1]) (seqS M [&π2])

    CBPV : CBPVCat ℓ (ℓ-max ℓ ℓ')
    CBPV .ob[_] = Ob
    CBPV .Hom[_][_,_] p = Tm (p .Prop→Type.pf)
    CBPV .idᴰ = idS
    CBPV ._⋆ᴰ_ = seqS
    CBPV .⋆IdLᴰ = IdLS
    CBPV .⋆IdRᴰ = IdRS
    CBPV .⋆Assocᴰ = AssocS
    CBPV .isSetHomᴰ = isSetTm

    module C = Fibers CBPV

    module Cop = Fibers (CBPV ^opᴰ)

    value-terminalⱽ : Terminalⱽ CBPV 𝒱
    value-terminalⱽ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' CBPV 𝒱 UnitPshᴰ
      ue .UniversalElementⱽ'.vertexⱽ = [1]
      ue .UniversalElementⱽ'.elementⱽ = tt
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .fst _ = [1I]
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .fst _ = refl
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .snd V = sym ([1η] V)

    value-productⱽ : ∀ A₁ A₂ → BinProductⱽ CBPV A₁ A₂
    value-productⱽ A₁ A₂ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' CBPV 𝒱 (BinProductⱽSpec CBPV A₁ A₂)
      ue .UniversalElementⱽ'.vertexⱽ = A₁ [×] A₂
      ue .UniversalElementⱽ'.elementⱽ = [×π1] , [×π2]
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .fst V = [×I] (V .fst) (V .snd)
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .fst V =
        ΣPathP
          ( C.rectifyOut {e' = refl}
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} ([×β1] (V .fst) (V .snd)))
          , C.rectifyOut {e' = refl}
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} ([×β2] (V .fst) (V .snd))))
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .snd V =
        cong₂ [×I]
          (C.rectifyOut {e' = refl} (C.reind-filler⁻ _))
          (C.rectifyOut {e' = refl} (C.reind-filler⁻ _))
        ∙ sym ([×η] V)

    value-initialⱽ : Initialⱽ CBPV 𝒱
    value-initialⱽ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' (CBPV ^opᴰ) 𝒱 UnitPshᴰ
      ue .UniversalElementⱽ'.vertexⱽ = [0]
      ue .UniversalElementⱽ'.elementⱽ = tt
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .fst _ = [0E]
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .snd .fst _ = refl
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .snd .snd V = sym ([0η] V)

    value-coproductⱽ : ∀ A₁ A₂ → BinCoProductⱽ CBPV A₁ A₂
    value-coproductⱽ A₁ A₂ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' (CBPV ^opᴰ) 𝒱
        (BinProductⱽSpec (CBPV ^opᴰ) A₁ A₂)
      ue .UniversalElementⱽ'.vertexⱽ = A₁ [+] A₂
      ue .UniversalElementⱽ'.elementⱽ = [+I1] , [+I2]
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .fst V = [+E] (V .fst) (V .snd)
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .snd .fst V =
        ΣPathP
          ( Cop.rectifyOut {e' = refl}
              (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} ([+β1] (V .fst) (V .snd)))
          , Cop.rectifyOut {e' = refl}
              (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} ([+β2] (V .fst) (V .snd))))
      ue .UniversalElementⱽ'.universalⱽ (k , A , f) .snd .snd V =
        cong₂ [+E]
          (Cop.rectifyOut {e' = refl} (Cop.reind-filler⁻ _))
          (Cop.rectifyOut {e' = refl} (Cop.reind-filler⁻ _))
        ∙ sym ([+η] V)

    computation-terminalⱽ : Terminalⱽ CBPV 𝒞
    computation-terminalⱽ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' CBPV 𝒞 UnitPshᴰ
      ue .UniversalElementⱽ'.vertexⱽ = [⊤]
      ue .UniversalElementⱽ'.elementⱽ = tt
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .fst _ = [⊤I]
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .snd .fst _ = refl
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .snd .snd M = sym ([⊤η] M)

    computation-productⱽ : ∀ B₁ B₂ → BinProductⱽ CBPV B₁ B₂
    computation-productⱽ B₁ B₂ = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' CBPV 𝒞 (BinProductⱽSpec CBPV B₁ B₂)
      ue .UniversalElementⱽ'.vertexⱽ = B₁ [&] B₂
      ue .UniversalElementⱽ'.elementⱽ = [&π1] , [&π2]
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .fst M = [&I] (M .fst) (M .snd)
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .snd .fst M =
        ΣPathP
          ( C.rectifyOut {e' = refl}
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} ([&β1] (M .fst) (M .snd)))
          , C.rectifyOut {e' = refl}
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} ([&β2] (M .fst) (M .snd))))
      ue .UniversalElementⱽ'.universalⱽ (k , B , f) .snd .snd M =
        cong₂ [&I]
          (C.rectifyOut {e' = refl} (C.reind-filler⁻ _))
          (C.rectifyOut {e' = refl} (C.reind-filler⁻ _))
        ∙ sym ([&η] M)

    [U]-UMPPath : hasU CBPV
    [U]-UMPPath B = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' CBPV 𝒱
        (CartesianLiftPshSpec (KIND [-, 𝒞 ]) CBPV (CBPV [-][-, B ]) (ı tt))
      ue .UniversalElementⱽ'.vertexⱽ = [U] B
      ue .UniversalElementⱽ'.elementⱽ = [force]
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .fst = [thunk]
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .fst M =
        C.rectifyOut {e' = refl}
          (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} ([Uβ] M))
      ue .UniversalElementⱽ'.universalⱽ (𝒱 , A , f) .snd .snd V =
        cong [thunk] (C.rectifyOut {e' = refl} (C.reind-filler⁻ _))
        ∙ sym ([Uη] V)

    [F]-UMPPath : hasF CBPV
    [F]-UMPPath A = UniversalElementⱽ'.REPRⱽ ue
      where
      ue : UniversalElementⱽ' (CBPV ^opᴰ) 𝒞
        (CartesianLiftPshSpec ((KIND ^op) [-, 𝒱 ]) (CBPV ^opᴰ)
          ((CBPV ^opᴰ) [-][-, A ]) (ı tt))
      ue .UniversalElementⱽ'.vertexⱽ = [F] A
      ue .UniversalElementⱽ'.elementⱽ = [ret]
      ue .UniversalElementⱽ'.universalⱽ (𝒞 , B , f) .fst = [bind]
      ue .UniversalElementⱽ'.universalⱽ (𝒞 , B , f) .snd .fst M =
        Cop.rectifyOut {e' = refl}
          (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} ([Fβ] M))
      ue .UniversalElementⱽ'.universalⱽ (𝒞 , B , f) .snd .snd K =
        cong [bind] (Cop.rectifyOut {e' = refl} (Cop.reind-filler⁻ _))
        ∙ sym ([Fη] K)

    MultCBPV : MultCBPVCat _ _
    MultCBPV = CBPV , [U]-UMPPath , [F]-UMPPath

    AddCBPV : AddCBPVCat _ _
    AddCBPV = MultCBPV , value-terminalⱽ , value-productⱽ
      , value-initialⱽ , value-coproductⱽ
      , computation-terminalⱽ , computation-productⱽ

-- Checkpoint for the subsequent displayed eliminator.  It must be supplied
-- with displayed universal elements over, respectively:
--
--   * D.snd.fst                         value terminal
--   * D.snd.snd.fst                    value binary products
--   * D.snd.snd.snd.fst                value initial
--   * D.snd.snd.snd.snd.fst            value binary coproducts
--   * D.snd.snd.snd.snd.snd.fst        computation terminal
--   * D.snd.snd.snd.snd.snd.snd        computation binary products
--
-- Each chosen displayed universal element must be stable under reindexing.
-- For coproduct elimination this stability is needed over both arrows out of
-- 𝒱; for computation-product introduction it is needed for sources in both
-- fibers.  No displayed-additive record is postulated here: its representation
-- and the formulation of these stability paths remain the user-owned API.
