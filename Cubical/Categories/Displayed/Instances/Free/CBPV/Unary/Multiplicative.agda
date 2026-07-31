-- CBPV syntax as a category displayed over 𝓥 → 𝓒 ala the Fibrational Framework

-- --lossy-unification here is a convenience for Tm to pick the most
-- general implicits automatically. It's not totally necessary.

-- Here's the plan.

-- U/F are symmetric so without loss of generality let's pick U since
-- it involves fewer `op`s.

-- The universal property of U B is that it is the cartesian lift of B along 𝓥 ≤ 𝓒.
-- This represents the displayed presheaf (yoRec ≤)*(CBPV [-][-, B ])

-- The displayed universal property for Uᴰ Bᴰ over U B is then a
-- presheaf displayed over ∫ (yoRec ≤)*(CBPV [-][-, B ]). There is a projection π : ∫ (yoRec ≤)*(CBPV [-][-, B ]) → ∫CBPV [-, (𝓒 , B)] and the displayed universal property is π * (Cᴰ [-][-, Bᴰ ]) over the representation of ∫ (yoRec ≤)*(CBPV [-][-, B ])
--
-- The vertical universal property for Uᴰ Bᴰ is a cartesian lift of
-- (𝓥≤𝓒 , [force])* Bᴰ so it represents

-- (yoRec (𝓥≤𝓒,[force]))*(Cᴰ [-][-, Bᴰ ])
--
-- which is a vertical presheaf over ∫CBPV [-, (𝓥 , [U] B) ]
--
-- so vertical implies displayed here bc we have
-- the displayed universal property is to represent the vertical (yoRec (𝓥≤𝓒,[force]))*π*
--
{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.Multiplicative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More

open import Cubical.Prop
open import Cubical.Data.Sigma
open import Cubical.Data.Bool as Bool hiding (elim)
import Cubical.Data.Equality as Eq

open import Cubical.Categories.Category hiding (isIso)
open import Cubical.Categories.Functor
open import Cubical.Categories.Functors.More
open import Cubical.Categories.Instances.WalkingArrow
  renaming (WalkingArrow to KIND; Vertex to Kind; l to 𝓥; r to 𝓒; ≤Vertex to ≤Kind)
open import Cubical.Categories.Instances.TotalCategory hiding (elim)
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Instances.Opposite
open import Cubical.Categories.Displayed.Instances.Reindex
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV
open import Cubical.Categories.Displayed.CBPV.Unary.Base

private
  variable
    ℓ ℓ' ℓ'' ℓᴰ ℓᴰ' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category
open Categoryᴰ
open Functor
open Section
open PshHom
open PshIso
open UniversalElement

module CBPV (BaseTy : Kind → Type ℓ)
  where
  data Ob : Kind → Type ℓ where
    gen : ∀ {k} → BaseTy k → Ob k
    [F] : Ob 𝓥 → Ob 𝓒
    [U] : Ob 𝓒 → Ob 𝓥

  VTy = Ob 𝓥
  CTy = Ob 𝓒
  module Terms (Fun : ∀ {k1 k2} → ≤Kind k1 k2 → Ob k1 → Ob k2 → Type ℓ') where
    -- WARNING: these are public
    variable
      k k' k1 k2 : Kind
      Δ Γ Θ Ξ : Ob k
      A A' A'' A1 A2 : VTy
      B B' B'' B1 B2 : CTy
      k≤ k≤' k≤'' : ≤Kind k1 k2

    data Tm : (k≤ : ≤Kind k1 k2) → Ob k1 → Ob k2 → Type (ℓ-max ℓ ℓ') where
      gen : Fun k≤ Γ Δ → Tm k≤ Γ Δ

      idS : ∀ {Γ : Ob k} → Tm (≤V-refl k) Γ Γ
      seqS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) → Tm (≤V-trans k≤ k≤') Γ Θ
      IdLS : (γ : Tm k≤ Δ Γ) → seqS idS γ ≡ γ
      IdRS : (γ : Tm k≤ Δ Γ) → seqS γ idS ≡ γ
      AssocS : (δ : Tm k≤ Γ Δ) (θ : Tm k≤' Δ Θ) (ξ : Tm k≤'' Θ Ξ)
        → seqS (seqS δ θ) ξ ≡ seqS δ (seqS θ ξ)
      isSetTm : isSet (Tm k≤ Γ Δ)

      -- [F] is an op-cartesian lift of the morphism 𝓥 → 𝓒
      [ret] : Tm _ A ([F] A)
      [bind] : Tm _ A B → Tm _ ([F] A) B
      [Fβ] : (M : Tm _ A B) → seqS [ret] ([bind] M) ≡ M
      [Fη] : (K : Tm _ ([F] A) B) → K ≡ [bind] (seqS [ret] K)

      -- [U] is a cartesian lift of the morphism 𝓥 → 𝓒
      [force] : Tm _ ([U] B) B
      [thunk] : Tm _ Γ B → Tm {k1 = 𝓥} _ Γ ([U] B)
      [Uβ] : (M : Tm _ A B) → seqS ([thunk] M) [force] ≡ M
      [Uη] : (V : Tm _ Γ ([U] B)) → V ≡ [thunk] (seqS V [force])

      -- Don't do these for now
      -- -- Effects: boolean state
      -- [read] : Tm _ A B → Tm _ A B → Tm _ A B
      -- [write] : Bool → Tm _ A B → Tm _ A B

      -- -- laws
      -- [rwβt] : (Mt Mf : Tm _ A B)
      --   → [write] true ([read] Mt Mf) ≡ [write] true Mt
      -- [rwβf] : (Mt Mf : Tm _ A B)
      --   → [write] false ([read] Mt Mf) ≡ [write] false Mf
      -- [rwη] : (M : Tm (≤V-r-⊤ _) Γ B)
      --   → M ≡ [read] ([write] true M) ([write] false M)

      -- -- homomorphism properties
      -- [r-homL] : (f : Tm _ A A')(Mt Mf : Tm _ A' B)
      --   → seqS f ([read] Mt Mf) ≡ [read] (seqS f Mt) (seqS f Mf)
      -- [r-homR] : (Mt Mf : Tm _ A B) (S : Tm _ B B')
      --   → seqS ([read] Mt Mf) S ≡ [read] (seqS Mt S) (seqS Mf S)
      -- [w-homL] : ∀ (f : Tm _ A A') b (M : Tm _ A' B)
      --   → seqS f ([write] b M) ≡ [write] b (seqS f M)
      -- [w-homR] : ∀ b (M : Tm _ A B) (S : Tm _ B B')
      --   → seqS ([write] b M) S ≡ [write] b (seqS M S)

    CBPV : CBPVCat ℓ (ℓ-max ℓ ℓ')
    CBPV .ob[_] = Ob
    CBPV .Hom[_][_,_] ≤ = Tm (≤ .Prop→Type.pf)
    CBPV .idᴰ = idS
    CBPV ._⋆ᴰ_ = seqS
    CBPV .⋆IdLᴰ = IdLS
    CBPV .⋆IdRᴰ = IdRS
    CBPV .⋆Assocᴰ = AssocS
    CBPV .isSetHomᴰ = isSetTm

    module CBPV = Fibers CBPV
    module CBPV^op = Fibers (CBPV ^opᴰ)

    open EqPsh.UEⱽ

    [U]-UMP : hasUEq CBPV
    [U]-UMP B = EqPsh.UEⱽ→Reprⱽ _ KIND-IdR [U]-ue
      where
      KIND-IdR : EqPsh.EqIdR KIND
      KIND-IdR _ = Eq.refl

      [U]-ue : EqPsh.CartesianLiftUE CBPV KINDAssoc KIND-IdR
        {x = 𝓥}{y = 𝓒} (ı tt) B
      [U]-ue .v = [U] B
      [U]-ue .e = [force]
      [U]-ue .universal .isPshIsoEq.nIso (𝓥 , A , f) .fst = [thunk]
      [U]-ue .universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .fst M = [Uβ] M
      [U]-ue .universal .isPshIsoEq.nIso (𝓥 , A , f) .snd .snd V = sym ([Uη] V)

    [F]-UMP : hasFEq CBPV
    [F]-UMP A = EqPsh.UEⱽ→Reprⱽ _ KIND^op-IdR [F]-ue
      where
      KIND^op-IdR : EqPsh.EqIdR (KIND ^op)
      KIND^op-IdR _ = Eq.refl

      [F]-ue : EqPsh.CartesianLiftUE (CBPV ^opᴰ)
        KIND^opAssoc KIND^op-IdR {x = 𝓒}{y = 𝓥} (ı tt) A
      [F]-ue .v = [F] A
      [F]-ue .e = [ret]
      [F]-ue .universal .isPshIsoEq.nIso (𝓒 , B , f) .fst = [bind]
      [F]-ue .universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .fst M = [Fβ] M
      [F]-ue .universal .isPshIsoEq.nIso (𝓒 , B , f) .snd .snd K = sym ([Fη] K)

    [U]-UMPPath : hasU CBPV
    [U]-UMPPath B = UniversalElementⱽ'.REPRⱽ [U]-ue
      where
      [U]-ue : UniversalElementⱽ' CBPV 𝓥
        (CartesianLiftPshSpec (KIND [-, 𝓒 ]) CBPV (CBPV [-][-, B ]) (ı tt))
      [U]-ue .UniversalElementⱽ'.vertexⱽ = [U] B
      [U]-ue .UniversalElementⱽ'.elementⱽ = [force]
      [U]-ue .UniversalElementⱽ'.universalⱽ (𝓥 , A , f) .fst = [thunk]
      [U]-ue .UniversalElementⱽ'.universalⱽ (𝓥 , A , f) .snd .fst M =
        CBPV.rectifyOut {e' = refl}
          (CBPV.reind-filler⁻ _ ∙ CBPV.≡in {pth = refl} ([Uβ] M))
      [U]-ue .UniversalElementⱽ'.universalⱽ (𝓥 , A , f) .snd .snd V =
        cong [thunk]
          (CBPV.rectifyOut {e' = refl} (CBPV.reind-filler⁻ _))
        ∙ sym ([Uη] V)

    [F]-UMPPath : hasF CBPV
    [F]-UMPPath A = UniversalElementⱽ'.REPRⱽ [F]-ue
      where
      [F]-ue : UniversalElementⱽ' (CBPV ^opᴰ) 𝓒
        (CartesianLiftPshSpec ((KIND ^op) [-, 𝓥 ]) (CBPV ^opᴰ)
          ((CBPV ^opᴰ) [-][-, A ]) (ı tt))
      [F]-ue .UniversalElementⱽ'.vertexⱽ = [F] A
      [F]-ue .UniversalElementⱽ'.elementⱽ = [ret]
      [F]-ue .UniversalElementⱽ'.universalⱽ (𝓒 , B , f) .fst = [bind]
      [F]-ue .UniversalElementⱽ'.universalⱽ (𝓒 , B , f) .snd .fst M =
        CBPV^op.rectifyOut {e' = refl}
          (CBPV^op.reind-filler⁻ _ ∙ CBPV^op.≡in {pth = refl} ([Fβ] M))
      [F]-ue .UniversalElementⱽ'.universalⱽ (𝓒 , B , f) .snd .snd K =
        cong [bind]
          (CBPV^op.rectifyOut {e' = refl} (CBPV^op.reind-filler⁻ _))
        ∙ sym ([Fη] K)

    MultCBPV : MultCBPVCat _ _
    MultCBPV = CBPV , [U]-UMPPath , [F]-UMPPath

    module Elim
      (Cᴰ : CBPVCatᴰ CBPV ℓᴰ ℓᴰ')
      (CᴰhasUᴰ : hasUᴰ Cᴰ (MultCBPV .snd .fst))
      (CᴰhasFᴰ : hasFᴰ Cᴰ (MultCBPV .snd .snd))
      where
      private
        module Cᴰ = Fibers Cᴰ
        module Cᴰ^op = Fibers (Cᴰ ^opᴰᴰ)

      module _
        (ı-Ob : ∀ {k} (X : BaseTy k) → Cᴰ.ob[ k , gen X ])
        where
        elim-F-obᴰ : ∀ Γ → Cᴰ.ob[ k , Γ ]
        elim-F-obᴰ (gen X) = ı-Ob X
        elim-F-obᴰ ([F] A) = CᴰhasFᴰ (elim-F-obᴰ A) .fst
        elim-F-obᴰ ([U] B) = CᴰhasUᴰ (elim-F-obᴰ B) .fst

        retᴰ : ∀ {A : VTy} → Cᴰ.Hom[ ı tt , [ret] ][ elim-F-obᴰ A , elim-F-obᴰ ([F] A) ]
        retᴰ = Cᴰ.reind
          (CBPV^op.reind-filler⁻ _
          ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))
          (CᴰhasFᴰ (elim-F-obᴰ _) .snd .fst .PshHom.N-ob _ Cᴰ^op.idᴰ)

        bindᴰ : ∀ {A : VTy}{B : CTy} (M : Tm tt A B)
          → Cᴰ.Hom[ ı tt , M ][ elim-F-obᴰ A , elim-F-obᴰ B ]
          → Cᴰ.Hom[ Category.id KIND , [bind] M ][ elim-F-obᴰ ([F] A) , elim-F-obᴰ B ]
        bindᴰ {A = A} M Mᴰ =
          CᴰhasFᴰ (elim-F-obᴰ A) .snd .snd _ _ .isIsoOver.inv _ Mᴰ

        Fβᴰ : ∀ {A : VTy}{B : CTy} (M : Tm tt A B)
          (Mᴰ : Cᴰ.Hom[ ı tt , M ][ elim-F-obᴰ A , elim-F-obᴰ B ])
          → Path Cᴰ.Hom[ _ , _ ] (_ , retᴰ Cᴰ.⋆ᴰ bindᴰ M Mᴰ) (_ , Mᴰ)
        Fβᴰ {A = A} M Mᴰ =
          Cᴰ.⟨ Cᴰ.reind-filler⁻
              (CBPV^op.reind-filler⁻ _
              ∙ CBPV^op.≡in {pth = refl} (IdRS [ret])) ⟩⋆⟨⟩
          ∙ Cᴰ^op.reind-filler
              {p = bindᴰ M Mᴰ Cᴰ^op.⋆ᴰ
                (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst .PshHom.N-ob _ Cᴰ^op.idᴰ)} _
          ∙ sym (∫PshHomᴰ
              (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst) .PshHom.N-hom _ _ _ _)
          ∙ cong (∫PshHomᴰ
              (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst) .PshHom.N-ob _)
              (sym (Cᴰ^op.reind-filler _) ∙ Cᴰ^op.⋆IdR _)
          ∙ Cᴰ^op.≡in
              (CᴰhasFᴰ (elim-F-obᴰ A) .snd .snd _ _
                .isIsoOver.rightInv _ Mᴰ)

        Fηᴰ : ∀ {A : VTy}{B : CTy} (K : Tm (≤V-refl 𝓒) ([F] A) B)
          (Kᴰ : Cᴰ.Hom[ Category.id KIND , K ][ elim-F-obᴰ ([F] A) , elim-F-obᴰ B ])
          → Path Cᴰ.Hom[ _ , _ ]
              (_ , Kᴰ)
              (_ , bindᴰ (seqS [ret] K) (retᴰ Cᴰ.⋆ᴰ Kᴰ))
        Fηᴰ {A = A} K Kᴰ =
          sym (Cᴰ^op.≡in
            (CᴰhasFᴰ (elim-F-obᴰ A) .snd .snd _ _
              .isIsoOver.leftInv _ Kᴰ))
          ∙ cong
              (invPshIso (∫PshIsoᴰ (CᴰhasFᴰ (elim-F-obᴰ A) .snd))
                .PshIso.trans .PshHom.N-ob _)
              (sym
                (Cᴰ^op.reind-filler
                  {p = Kᴰ Cᴰ^op.⋆ᴰ
                    (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst
                      .PshHom.N-ob _ Cᴰ^op.idᴰ)} _
                ∙ sym (∫PshHomᴰ
                    (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst)
                    .PshHom.N-hom _ _ _ _)
                ∙ cong (∫PshHomᴰ
                    (CᴰhasFᴰ (elim-F-obᴰ A) .snd .fst)
                    .PshHom.N-ob _)
                    (sym (Cᴰ^op.reind-filler _) ∙ Cᴰ^op.⋆IdR _))
              ∙ Cᴰ^op.⟨⟩⋆⟨ Cᴰ.reind-filler
                  (CBPV^op.reind-filler⁻ _
                  ∙ CBPV^op.≡in {pth = refl} (IdRS [ret])) ⟩)

        module _
          (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ)
            → Cᴰ.Hom[ ı k≤ , gen M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ])
          where
          elim-F-homᴰ : (M : Tm k≤ Γ Δ)
            → Cᴰ.Hom[ ı k≤ , M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ]
          elim-F-homᴰ (gen f) = ı-Fun f
          elim-F-homᴰ idS = Cᴰ.idᴰ
          elim-F-homᴰ (seqS M N) = elim-F-homᴰ M Cᴰ.⋆ᴰ elim-F-homᴰ N
          elim-F-homᴰ (IdLS M i) = Cᴰ.⋆IdLᴰ (elim-F-homᴰ M) i
          elim-F-homᴰ (IdRS M i) = Cᴰ.⋆IdRᴰ (elim-F-homᴰ M) i
          elim-F-homᴰ (AssocS L M N i) =
            Cᴰ.⋆Assocᴰ (elim-F-homᴰ L) (elim-F-homᴰ M) (elim-F-homᴰ N) i
          elim-F-homᴰ (isSetTm M N p q i j) = isSet→isSetDep
            (λ _ → Cᴰ.isSetHomᴰ)
            (elim-F-homᴰ M)
            (elim-F-homᴰ N)
            (cong elim-F-homᴰ p)
            (cong elim-F-homᴰ q)
            (isSetTm M N p q)
            i j
          elim-F-homᴰ [ret] = retᴰ
          elim-F-homᴰ ([bind] M) = bindᴰ M (elim-F-homᴰ M)
          elim-F-homᴰ ([Fβ] M i) =
            Cᴰ.rectify {e' = λ i → ı tt , [Fβ] M i}
              (Cᴰ.≡out (Fβᴰ M (elim-F-homᴰ M))) i
          elim-F-homᴰ ([Fη] K i) =
            Cᴰ.rectify {e' = λ i → Category.id KIND , [Fη] K i}
              (Cᴰ.≡out (Fηᴰ K (elim-F-homᴰ K))) i
          elim-F-homᴰ [force] = Cᴰ.reind
            (CBPV.reind-filler⁻ _ ∙ CBPV.≡in {pth = refl} (IdLS [force]))
            (forceᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ)
          elim-F-homᴰ ([thunk] M) =
            thunkᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ M (elim-F-homᴰ M)
          elim-F-homᴰ ([Uβ] M i) =
            Cᴰ.rectify {e' = λ i → ı tt , [Uβ] M i}
              (Cᴰ.≡out
                (Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler⁻
                    (CBPV.reind-filler⁻ _ ∙ CBPV.≡in {pth = refl} (IdLS [force])) ⟩
                ∙ Uβᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ
                    M (elim-F-homᴰ M))) i
          elim-F-homᴰ ([Uη] V i) =
            Cᴰ.rectify {e' = λ i → Category.id KIND , [Uη] V i}
              (Cᴰ.≡out
                (Uηᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ
                    V (elim-F-homᴰ V)
                ∙ cong-thunkᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ
                    (Cᴰ.⟨⟩⋆⟨ Cᴰ.reind-filler
                      (CBPV.reind-filler⁻ _
                      ∙ CBPV.≡in {pth = refl} (IdLS [force])) ⟩))) i

          elim : GlobalSection Cᴰ
          elim .F-obᴰ d = elim-F-obᴰ (d .snd)
          elim .F-homᴰ f = elim-F-homᴰ (f .snd)
          elim .F-idᴰ = refl
          elim .F-seqᴰ _ _ = refl

    module LocalElim
      {C : CBPVCat ℓD ℓD'}
      (F : Functorⱽ CBPV C)
      (Cⱽ : MultCBPVCatⱽ C ℓCᴰ ℓCᴰ')
      where
      private
        module Cᴰ = Fibers (Cⱽ .fst)

        reindexed : MultCBPVCatᴰ MultCBPV ℓCᴰ ℓCᴰ'
        reindexed = MultCBPVCatⱽ→ᴰ (MultCBPVCatⱽReindex Cⱽ F)

      module _
        (ı-ob : ∀ {k} (X : BaseTy k)
          → Cᴰ.ob[ k , F .Functorᴰ.F-obᴰ (gen X) ])
        where
        local-obᴰ : ∀ Γ → Cᴰ.ob[ k , F .Functorᴰ.F-obᴰ Γ ]
        local-obᴰ = Elim.elim-F-obᴰ
          (reindexed .fst)
          (reindexed .snd .fst)
          (reindexed .snd .snd)
          ı-ob

        localElim :
          (ı-hom : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ)
            → Cᴰ.Hom[ _ , F .Functorᴰ.F-homᴰ (gen M) ][ local-obᴰ Γ , local-obᴰ Δ ])
          → Section (∫F F) (Cⱽ .fst)
        localElim ı-hom =
          GlobalSectionReindex→Section (Cⱽ .fst) (∫F F)
            (Elim.elim
              (reindexed .fst)
              (reindexed .snd .fst)
              (reindexed .snd .snd)
              ı-ob
              ı-hom)
