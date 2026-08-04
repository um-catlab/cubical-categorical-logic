{-# OPTIONS --lossy-unification --prop #-}
module Cubical.Categories.Displayed.Instances.Free.CBPV.Unary.BoolState where

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
open import Cubical.Algebra.State
open import Cubical.Categories.Displayed.CBPV.Unary.StateAlgEnrichment

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

      -- Effects: boolean state
      [rd] : Tm _ A B → Tm _ A B → Tm _ A B
      [wt] : Bool → Tm _ A B → Tm _ A B

      -- -- laws
      [wt-rd] : ∀ b (Mt Mf : Tm _ A B)
        → [wt] b ([rd] Mt Mf) ≡ [wt] b (if b then Mt else Mf)
      [rd-wt] : (M : Tm _ A B)
        → M ≡ [rd] ([wt] true M) ([wt] false M)
      [wt-wt] : ∀ b1 b2 (M : Tm _ A B) → ([wt] b1 $ [wt] b2 M) ≡ [wt] b2 M

      -- -- homomorphism properties
      [r-homL] : (f : Tm _ A A')(Mt Mf : Tm _ A' B)
        → seqS f ([rd] Mt Mf) ≡ [rd] (seqS f Mt) (seqS f Mf)
      [r-homR] : (Mt Mf : Tm _ A B) (S : Tm _ B B')
        → seqS ([rd] Mt Mf) S ≡ [rd] (seqS Mt S) (seqS Mf S)
      [w-homL] : ∀ (f : Tm _ A A') b (M : Tm _ A' B)
        → seqS f ([wt] b M) ≡ [wt] b (seqS f M)
      [w-homR] : ∀ b (M : Tm _ A B) (S : Tm _ B B')
        → seqS ([wt] b M) S ≡ [wt] b (seqS M S)

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

    open StateAlg
    StateAlgEff : ∀ (A : Ob 𝓥)(B : Ob 𝓒) → StateAlg (CBPV [ _ ][ A , B ])
    StateAlgEff A B .rd = [rd]
    StateAlgEff A B .wt = [wt]
    StateAlgEff A B .wt-rd = [wt-rd]
    StateAlgEff A B .rd-wt = [rd-wt]
    StateAlgEff A B .wt-wt = [wt-wt]

    Subst-Homo : ∀ {A A'} (V : Tm _ A A') B
      → Homo (seqS {k≤ = tt} V) (StateAlgEff A' B) (StateAlgEff A B)
    Subst-Homo V B .Homo.rd-hom xt xf rdtf p =
      J (λ rdtf p → seqS V rdtf ≡ rd (StateAlgEff _ B)
          (seqS V xt) (seqS V xf))
        ([r-homL] V xt xf) (sym p)
    Subst-Homo V B .Homo.wt-hom b x wtbx p =
      J (λ wtbx p → seqS V wtbx ≡ wt (StateAlgEff _ B) b (seqS V x))
        ([w-homL] V b x) (sym p)

    Plug-Homo : ∀ {B B'} (S : Tm _ B B') A
      → Homo (λ M → seqS {k≤' = tt} M S) (StateAlgEff A B) (StateAlgEff A B')
    Plug-Homo S A .Homo.rd-hom xt xf rdtf p =
      J (λ rdtf p → seqS rdtf S ≡ rd (StateAlgEff A _)
          (seqS xt S) (seqS xf S))
        ([r-homR] xt xf S) (sym p)
    Plug-Homo S A .Homo.wt-hom b x wtbx p =
      J (λ wtbx p → seqS wtbx S ≡ wt (StateAlgEff A _) b (seqS x S))
        ([w-homR] b x S) (sym p)

    CBPVState : StateAlgEnrichment CBPV
    CBPVState .fst = StateAlgEff
    CBPVState .snd .fst = Subst-Homo
    CBPVState .snd .snd = Plug-Homo

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

        module _
          (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ)
            → Cᴰ.Hom[ ı k≤ , gen M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ])
          (StateAlgEffᴰ : ∀ {A B}(Aᴰ : Cᴰ.ob[ _ , A ])(Bᴰ : Cᴰ.ob[ _ , B ])
            → StateAlgᴰ (StateAlgEff A B) (λ M → Cᴰ.Hom[ _ , M ][ Aᴰ , Bᴰ ]))
          (Subst-Homoᴰ : ∀ {A A' B}
            {Aᴰ : Cᴰ.ob[ _ , A ]}{Aᴰ' : Cᴰ.ob[ _ , A' ]}{Bᴰ : Cᴰ.ob[ _ , B ]}
            {V : Tm _ A A'}
            (Vᴰ : Cᴰ.Hom[ _ , V ][ Aᴰ , Aᴰ' ])
            → Homoᴰ (λ _ → Vᴰ Cᴰ.⋆ᴰ_) (Subst-Homo V B) (StateAlgEffᴰ Aᴰ' Bᴰ) (StateAlgEffᴰ Aᴰ Bᴰ))
          (Plug-Homoᴰ : ∀ {A B B'}
            {Aᴰ : Cᴰ.ob[ _ , A ]}{Bᴰ : Cᴰ.ob[ _ , B ]}{Bᴰ' : Cᴰ.ob[ _ , B' ]}
            {S : Tm _ B B'}
            (Sᴰ : Cᴰ.Hom[ _ , S ][ Bᴰ , Bᴰ' ])
            → Homoᴰ (λ a → Cᴰ._⋆ᴰ Sᴰ) (Plug-Homo S A) (StateAlgEffᴰ Aᴰ Bᴰ) (StateAlgEffᴰ Aᴰ Bᴰ'))
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
            Fβᴰ Cᴰ (MultCBPV .snd .snd) CᴰhasFᴰ
              (CBPV^op.reind-filler⁻ _
              ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))
              M (λ i → ı tt , [Fβ] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ ([Fη] K i) =
            Fηᴰ Cᴰ (MultCBPV .snd .snd) CᴰhasFᴰ
              (CBPV^op.reind-filler⁻ _
              ∙ CBPV^op.≡in {pth = refl} (IdRS [ret]))
              K (λ i → Category.id KIND , [Fη] K i) (elim-F-homᴰ K) i
          elim-F-homᴰ [force] = Cᴰ.reind
            (CBPV.reind-filler⁻ _ ∙ CBPV.≡in {pth = refl} (IdLS [force]))
            (forceᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ)
          elim-F-homᴰ ([thunk] M) =
            thunkᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ M (elim-F-homᴰ M)
          elim-F-homᴰ ([Uβ] M i) =
            Uβᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ
              (CBPV.reind-filler⁻ _
              ∙ CBPV.≡in {pth = refl} (IdLS [force]))
              M (λ i → ı tt , [Uβ] M i) (elim-F-homᴰ M) i
          elim-F-homᴰ ([Uη] V i) =
            Uηᴰ Cᴰ (MultCBPV .snd .fst) CᴰhasUᴰ
              (CBPV.reind-filler⁻ _
              ∙ CBPV.≡in {pth = refl} (IdLS [force]))
              V (λ i → Category.id KIND , [Uη] V i) (elim-F-homᴰ V) i
          elim-F-homᴰ ([rd] Mt Mf) =
            StateAlgᴰ.rdᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              (elim-F-homᴰ Mt) (elim-F-homᴰ Mf)
          elim-F-homᴰ ([wt] b M) =
            StateAlgᴰ.wtᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              b (elim-F-homᴰ M)
          elim-F-homᴰ ([wt-rd] false Mt Mf i) =
            StateAlgᴰ.wt-rdᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              false Mt Mf (elim-F-homᴰ Mt) (elim-F-homᴰ Mf) i
          elim-F-homᴰ ([wt-rd] true Mt Mf i) =
            StateAlgᴰ.wt-rdᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              true Mt Mf (elim-F-homᴰ Mt) (elim-F-homᴰ Mf) i
          elim-F-homᴰ ([rd-wt] M i) =
            StateAlgᴰ.rd-wtᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              M (elim-F-homᴰ M) i
          elim-F-homᴰ ([wt-wt] b1 b2 M i) =
            StateAlgᴰ.wt-wtᴰ
              (StateAlgEffᴰ (elim-F-obᴰ _) (elim-F-obᴰ _))
              b1 b2 M (elim-F-homᴰ M) i
          elim-F-homᴰ ([r-homL] V Mt Mf i) =
            hSetReasoning.Prectify (_ , isSetTm)
              (λ N → Cᴰ.Hom[ ı _ , N ][ elim-F-obᴰ _ , elim-F-obᴰ _ ])
              {e' = λ j → [r-homL] V Mt Mf j}
              (Homoᴰ.rd-homᴰ' (Subst-Homoᴰ (elim-F-homᴰ V))
                Mt Mf (elim-F-homᴰ Mt) (elim-F-homᴰ Mf)) i
          elim-F-homᴰ ([r-homR] Mt Mf S i) =
            hSetReasoning.Prectify (_ , isSetTm)
              (λ N → Cᴰ.Hom[ ı _ , N ][ elim-F-obᴰ _ , elim-F-obᴰ _ ])
              {e' = λ j → [r-homR] Mt Mf S j}
              (Homoᴰ.rd-homᴰ' (Plug-Homoᴰ (elim-F-homᴰ S))
                Mt Mf (elim-F-homᴰ Mt) (elim-F-homᴰ Mf)) i
          elim-F-homᴰ ([w-homL] V b M i) =
            hSetReasoning.Prectify (_ , isSetTm)
              (λ N → Cᴰ.Hom[ ı _ , N ][ elim-F-obᴰ _ , elim-F-obᴰ _ ])
              {e' = λ j → [w-homL] V b M j}
              (Homoᴰ.wt-homᴰ' (Subst-Homoᴰ (elim-F-homᴰ V))
                b M (elim-F-homᴰ M)) i
          elim-F-homᴰ ([w-homR] b M S i) =
            hSetReasoning.Prectify (_ , isSetTm)
              (λ N → Cᴰ.Hom[ ı _ , N ][ elim-F-obᴰ _ , elim-F-obᴰ _ ])
              {e' = λ j → [w-homR] b M S j}
              (Homoᴰ.wt-homᴰ' (Plug-Homoᴰ (elim-F-homᴰ S))
                b M (elim-F-homᴰ M)) i

          elim : GlobalSection Cᴰ
          elim .F-obᴰ d = elim-F-obᴰ (d .snd)
          elim .F-homᴰ f = elim-F-homᴰ (f .snd)
          elim .F-idᴰ = refl
          elim .F-seqᴰ _ _ = refl

    module LocalElim
      {C : CBPVCat ℓD ℓD'}
      (F : Functorⱽ CBPV C)
      (Cⱽ : MultCBPVCatⱽ C ℓCᴰ ℓCᴰ')
      (CState : StateAlgEnrichment C)
      (FState : PreservesStateAlgEnrichment F CBPVState CState)
      (CᴰState : StateAlgEnrichmentᴰ CState (Cⱽ .fst))
      where
      private
        module Cᴰ = Fibers (Cⱽ .fst)

        reindexed : MultCBPVCatᴰ MultCBPV ℓCᴰ ℓCᴰ'
        reindexed = MultCBPVCatⱽ→ᴰ (MultCBPVCatⱽReindex Cⱽ F)

        reindexedState : StateAlgEnrichmentᴰ CBPVState (reindexed .fst)
        reindexedState = StateAlgEnrichmentᴰReindex
          F CBPVState CState FState (Cⱽ .fst) CᴰState

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
          (ı-hom : ∀ {k1 k2 Γ Δ} {k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ)
            → Cᴰ.Hom[ _ , F .Functorᴰ.F-homᴰ (gen M) ][
                local-obᴰ Γ , local-obᴰ Δ ])
          → Section (∫F F) (Cⱽ .fst)
        localElim ı-hom =
          GlobalSectionReindex→Section (Cⱽ .fst) (∫F F)
            (Elim.elim
              (reindexed .fst)
              (reindexed .snd .fst)
              (reindexed .snd .snd)
              ı-ob
              ı-hom
              (reindexedState .fst)
              (reindexedState .snd .fst)
              (reindexedState .snd .snd))
