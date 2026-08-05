-- Parameterized unary CBPV syntax with finite value (co)products and
-- finite computation products.
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Additive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.More
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
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
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
open PshHom
open isIsoOver
open Section

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

    module Elim (D : AddCBPVCatᴰ AddCBPV ℓ ℓ') where
      private
        Dᴰ = D .fst .fst
        module Dᴰ = Fibers Dᴰ
        module Dᴰop = Fibers (Dᴰ ^opᴰᴰ)

      module _ (ı-Ob : ∀ {k} (X : BaseTy k) → Dᴰ.ob[ k , gen X ]) where
        elim-F-obᴰ : ∀ {k} (X : Ob k) → Dᴰ.ob[ k , X ]
        elim-F-obᴰ (gen X) = ı-Ob X
        elim-F-obᴰ ([F] A) = D .fst .snd .snd (elim-F-obᴰ A) .fst
        elim-F-obᴰ ([U] B) = D .fst .snd .fst (elim-F-obᴰ B) .fst
        elim-F-obᴰ [1] = D .snd .fst .fst
        elim-F-obᴰ (A₁ [×] A₂) =
          D .snd .snd .fst A₁ A₂ (elim-F-obᴰ A₁) (elim-F-obᴰ A₂) .fst
        elim-F-obᴰ [0] = D .snd .snd .snd .fst .fst
        elim-F-obᴰ (A₁ [+] A₂) =
          D .snd .snd .snd .snd .fst A₁ A₂ (elim-F-obᴰ A₁) (elim-F-obᴰ A₂) .fst
        elim-F-obᴰ [⊤] = D .snd .snd .snd .snd .snd .fst .fst
        elim-F-obᴰ (B₁ [&] B₂) =
          D .snd .snd .snd .snd .snd .snd B₁ B₂ (elim-F-obᴰ B₁) (elim-F-obᴰ B₂) .fst

        private
          module DA = AddCBPVCatᴰNotation AddCBPV D

          value-π₁≡[×π1] : ∀ {A₁ A₂} →
            BinProductⱽNotation.π₁ CBPV (value-productⱽ A₁ A₂) ≡ [×π1]
          value-π₁≡[×π1] = C.rectifyOut {e' = refl}
            (C.reind-filler⁻ (Category.⋆IdR KIND _) ∙ C.≡in {pth = refl} (IdLS [×π1]))

          value-π₂≡[×π2] : ∀ {A₁ A₂} →
            BinProductⱽNotation.π₂ CBPV (value-productⱽ A₁ A₂) ≡ [×π2]
          value-π₂≡[×π2] = C.rectifyOut {e' = refl}
            (C.reind-filler⁻ (Category.⋆IdR KIND _) ∙ C.≡in {pth = refl} (IdLS [×π2]))

          value-σ₁≡[+I1] : ∀ {A₁ A₂} →
            BinProductⱽNotation.π₁ (CBPV ^opᴰ) (value-coproductⱽ A₁ A₂) ≡ [+I1]
          value-σ₁≡[+I1] = Cop.rectifyOut {e' = refl}
            (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _) ∙ Cop.≡in {pth = refl} (IdRS [+I1]))

          value-σ₂≡[+I2] : ∀ {A₁ A₂} →
            BinProductⱽNotation.π₂ (CBPV ^opᴰ) (value-coproductⱽ A₁ A₂) ≡ [+I2]
          value-σ₂≡[+I2] = Cop.rectifyOut {e' = refl}
            (Cop.reind-filler⁻ (Category.⋆IdR (KIND ^op) _) ∙ Cop.≡in {pth = refl} (IdRS [+I2]))

          computation-π₁≡[&π1] : ∀ {B₁ B₂} →
            BinProductⱽNotation.π₁ CBPV (computation-productⱽ B₁ B₂) ≡ [&π1]
          computation-π₁≡[&π1] = C.rectifyOut {e' = refl}
            (C.reind-filler⁻ (Category.⋆IdR KIND _) ∙ C.≡in {pth = refl} (IdLS [&π1]))

          computation-π₂≡[&π2] : ∀ {B₁ B₂} →
            BinProductⱽNotation.π₂ CBPV (computation-productⱽ B₁ B₂) ≡ [&π2]
          computation-π₂≡[&π2] = C.rectifyOut {e' = refl}
            (C.reind-filler⁻ (Category.⋆IdR KIND _) ∙ C.≡in {pth = refl} (IdLS [&π2]))

        retᴰ : ∀ {A} → Dᴰ.Hom[ ı tt , [ret] ][ elim-F-obᴰ A , elim-F-obᴰ ([F] A) ]
        retᴰ = Dᴰ.reind
          (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} (IdRS [ret]))
          (D .fst .snd .snd (elim-F-obᴰ _) .snd .fst .PshHom.N-ob _ Dᴰop.idᴰ)

        bindᴰ : ∀ {A B} (M : Tm _ A B)
          → Dᴰ.Hom[ ı tt , M ][ elim-F-obᴰ A , elim-F-obᴰ B ]
          → Dᴰ.Hom[ Category.id KIND , [bind] M ][ elim-F-obᴰ ([F] A) , elim-F-obᴰ B ]
        bindᴰ {A = A} M Mᴰ = D .fst .snd .snd (elim-F-obᴰ A)
          .snd .snd _ _ .isIsoOver.inv _ Mᴰ

        module _
          (ı-Fun : ∀ {k₁ k₂ Γ Δ} {k≤ : ≤Kind k₁ k₂} (M : Fun k≤ Γ Δ)
            → Dᴰ.Hom[ ı k≤ , gen M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ])
          where
          elim-F-homᴰ : (M : Tm k≤ Γ Δ)
            → Dᴰ.Hom[ ı k≤ , M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ]
          elim-F-homᴰ (gen f) = ı-Fun f
          elim-F-homᴰ idS = Dᴰ.idᴰ
          elim-F-homᴰ (seqS M N) = elim-F-homᴰ M Dᴰ.⋆ᴰ elim-F-homᴰ N
          elim-F-homᴰ (IdLS M i) = Dᴰ.⋆IdLᴰ (elim-F-homᴰ M) i
          elim-F-homᴰ (IdRS M i) = Dᴰ.⋆IdRᴰ (elim-F-homᴰ M) i
          elim-F-homᴰ (AssocS L M N i) =
            Dᴰ.⋆Assocᴰ (elim-F-homᴰ L) (elim-F-homᴰ M) (elim-F-homᴰ N) i
          elim-F-homᴰ (isSetTm M N p q i j) = isSet→isSetDep
            (λ _ → Dᴰ.isSetHomᴰ) (elim-F-homᴰ M) (elim-F-homᴰ N)
            (cong elim-F-homᴰ p) (cong elim-F-homᴰ q) (isSetTm M N p q) i j
          elim-F-homᴰ [ret] = retᴰ
          elim-F-homᴰ ([bind] M) = bindᴰ M (elim-F-homᴰ M)
          elim-F-homᴰ ([Fβ] M i) =
            Fβᴰ Dᴰ (MultCBPV .snd .snd) (D .fst .snd .snd)
              (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} (IdRS [ret]))
              M (λ i → ı tt , [Fβ] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ ([Fη] K i) =
            Fηᴰ Dᴰ (MultCBPV .snd .snd) (D .fst .snd .snd)
              (Cop.reind-filler⁻ _ ∙ Cop.≡in {pth = refl} (IdRS [ret]))
              K (λ i → Category.id KIND , [Fη] K i) (elim-F-homᴰ K) i
          elim-F-homᴰ [force] = Dᴰ.reind
            (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} (IdLS [force]))
            (forceᴰ Dᴰ (MultCBPV .snd .fst) (D .fst .snd .fst))
          elim-F-homᴰ ([thunk] M) =
            thunkᴰ Dᴰ (MultCBPV .snd .fst) (D .fst .snd .fst) M (elim-F-homᴰ M)
          elim-F-homᴰ ([Uβ] M i) =
            Uβᴰ Dᴰ (MultCBPV .snd .fst) (D .fst .snd .fst)
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} (IdLS [force]))
              M (λ i → ı tt , [Uβ] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ ([Uη] V i) =
            Uηᴰ Dᴰ (MultCBPV .snd .fst) (D .fst .snd .fst)
              (C.reind-filler⁻ _ ∙ C.≡in {pth = refl} (IdLS [force]))
              V (λ i → Category.id KIND , [Uη] V i) (elim-F-homᴰ V) i
          elim-F-homᴰ [1I] = Dᴰ.reind (ΣPathP (refl , refl)) DA.value-terminal-introᴰ
          elim-F-homᴰ ([1η] V i) =
            DA.value-terminal-ηᴰ (ΣPathP (refl , refl))
              (λ i → ı _ , [1η] V i)
              (elim-F-homᴰ V) i
          elim-F-homᴰ ([×I] V₁ V₂) = Dᴰ.reind (ΣPathP (refl , refl))
            (DA.value-pairᴰ (elim-F-obᴰ _) (elim-F-obᴰ _)
              (elim-F-homᴰ V₁) (elim-F-homᴰ V₂))
          elim-F-homᴰ [×π1] = Dᴰ.reind
            (ΣPathP (refl , value-π₁≡[×π1]))
            (DA.value-πᴰ₁ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ [×π2] = Dᴰ.reind
            (ΣPathP (refl , value-π₂≡[×π2]))
            (DA.value-πᴰ₂ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ ([×β1] V₁ V₂ i) =
            DA.value-×βᴰ₁-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , value-π₁≡[×π1]))
              (λ i → ı _ , [×β1] V₁ V₂ i)
              (elim-F-homᴰ V₁) (elim-F-homᴰ V₂) i
          elim-F-homᴰ ([×β2] V₁ V₂ i) =
            DA.value-×βᴰ₂-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , value-π₂≡[×π2]))
              (λ i → ı _ , [×β2] V₁ V₂ i)
              (elim-F-homᴰ V₁) (elim-F-homᴰ V₂) i
          elim-F-homᴰ ([×η] M i) =
            DA.value-×ηᴰ-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              value-π₁≡[×π1] value-π₂≡[×π2]
              (λ i → ı _ , [×η] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ [0E] = Dᴰ.reind (ΣPathP (refl , refl)) DA.value-initial-elimᴰ
          elim-F-homᴰ ([0η] M i) =
            DA.value-initial-ηᴰ (ΣPathP (refl , refl))
              (λ i → ı _ , [0η] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ [+I1] = Dᴰ.reind
            (ΣPathP (refl , value-σ₁≡[+I1]))
            (DA.value-σᴰ₁ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ [+I2] = Dᴰ.reind
            (ΣPathP (refl , value-σ₂≡[+I2]))
            (DA.value-σᴰ₂ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ ([+E] f g) = Dᴰ.reind (ΣPathP (refl , refl))
            (DA.value-copairᴰ (elim-F-obᴰ _) (elim-F-obᴰ _)
              (elim-F-homᴰ f) (elim-F-homᴰ g))
          elim-F-homᴰ ([+β1] M₁ M₂ i) =
            DA.value-+βᴰ₁-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , value-σ₁≡[+I1]))
              (λ i → ı _ , [+β1] M₁ M₂ i)
              (elim-F-homᴰ M₁) (elim-F-homᴰ M₂) i
          elim-F-homᴰ ([+β2] M₁ M₂ i) =
            DA.value-+βᴰ₂-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , value-σ₂≡[+I2]))
              (λ i → ı _ , [+β2] M₁ M₂ i)
              (elim-F-homᴰ M₁) (elim-F-homᴰ M₂) i
          elim-F-homᴰ ([+η] M i) =
            DA.value-+ηᴰ-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              value-σ₁≡[+I1] value-σ₂≡[+I2]
              (λ i → ı _ , [+η] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ [⊤I] = Dᴰ.reind (ΣPathP (refl , refl)) DA.computation-terminal-introᴰ
          elim-F-homᴰ ([⊤η] M i) =
            DA.computation-terminal-ηᴰ (ΣPathP (refl , refl))
              (λ i → ı _ , [⊤η] M i)
              (elim-F-homᴰ M) i
          elim-F-homᴰ ([&I] M₁ M₂) = Dᴰ.reind (ΣPathP (refl , refl))
            (DA.computation-pairᴰ (elim-F-obᴰ _) (elim-F-obᴰ _)
              (elim-F-homᴰ M₁) (elim-F-homᴰ M₂))
          elim-F-homᴰ [&π1] = Dᴰ.reind
            (ΣPathP (refl , computation-π₁≡[&π1]))
            (DA.computation-πᴰ₁ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ [&π2] = Dᴰ.reind
            (ΣPathP (refl , computation-π₂≡[&π2]))
            (DA.computation-πᴰ₂ (elim-F-obᴰ _) (elim-F-obᴰ _))
          elim-F-homᴰ ([&β1] M₁ M₂ i) =
            DA.computation-×βᴰ₁-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , computation-π₁≡[&π1]))
              (λ i → ı _ , [&β1] M₁ M₂ i)
              (elim-F-homᴰ M₁) (elim-F-homᴰ M₂) i
          elim-F-homᴰ ([&β2] M₁ M₂ i) =
            DA.computation-×βᴰ₂-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              (ΣPathP (refl , computation-π₂≡[&π2]))
              (λ i → ı _ , [&β2] M₁ M₂ i)
              (elim-F-homᴰ M₁) (elim-F-homᴰ M₂) i
          elim-F-homᴰ ([&η] M i) =
            DA.computation-×ηᴰ-on (elim-F-obᴰ _) (elim-F-obᴰ _)
              computation-π₁≡[&π1] computation-π₂≡[&π2]
              (λ i → ı _ , [&η] M i) (elim-F-homᴰ M) i

          elim : GlobalSection Dᴰ
          elim .F-obᴰ d = elim-F-obᴰ (d .snd)
          elim .F-homᴰ f = elim-F-homᴰ (f .snd)
          elim .F-idᴰ = refl
          elim .F-seqᴰ _ _ = refl
