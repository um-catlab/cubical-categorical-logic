-- CBPV syntax as a category displayed over 𝓥 → 𝓒 ala the Fibrational Framework

-- --lossy-unification here is a convenience for Tm to pick the most
-- general implicits automatically
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
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Base
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Fibration
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Base as EqPsh
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Eq.Conversion.CartesianV

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
      [read] : Tm _ A B → Tm _ A B → Tm _ A B
      [write] : Bool → Tm _ A B → Tm _ A B

      -- laws
      [rwβt] : (Mt Mf : Tm _ A B)
        → [write] true ([read] Mt Mf) ≡ [write] true Mt
      [rwβf] : (Mt Mf : Tm _ A B)
        → [write] false ([read] Mt Mf) ≡ [write] false Mf
      [rwη] : (M : Tm (≤V-r-⊤ _) Γ B)
        → M ≡ [read] ([write] true M) ([write] false M)

      -- homomorphism properties
      [r-homL] : (f : Tm _ A A')(Mt Mf : Tm _ A' B)
        → seqS f ([read] Mt Mf) ≡ [read] (seqS f Mt) (seqS f Mf)
      [r-homR] : (Mt Mf : Tm _ A B) (S : Tm _ B B')
        → seqS ([read] Mt Mf) S ≡ [read] (seqS Mt S) (seqS Mf S)
      [w-homL] : ∀ (f : Tm _ A A') b (M : Tm _ A' B)
        → seqS f ([write] b M) ≡ [write] b (seqS f M)
      [w-homR] : ∀ b (M : Tm _ A B) (S : Tm _ B B')
        → seqS ([write] b M) S ≡ [write] b (seqS M S)

    CBPV : Categoryᴰ KIND ℓ (ℓ-max ℓ ℓ')
    CBPV .ob[_] = Ob
    CBPV .Hom[_][_,_] ≤ = Tm (≤ .Prop→Type.pf)
    CBPV .idᴰ = idS
    CBPV ._⋆ᴰ_ = seqS
    CBPV .⋆IdLᴰ = IdLS
    CBPV .⋆IdRᴰ = IdRS
    CBPV .⋆Assocᴰ = AssocS
    CBPV .isSetHomᴰ = isSetTm

    module CBPV = Categoryᴰ CBPV

    open EqPsh.UEⱽ

    -- What is the universal property of [U]? It is that of a cartesian lift.
    --
    -- That is, there is a morphism ≤ : 𝓥 → 𝓒 and this is the cartesian lift ≤*B
    --
    -- The presheaf it represents is (yoRec ≤)* (CBPV [-][-, B ]) : Pshⱽ 𝓥 CBPV
    -- which is of course the same as Pshᴰ (KIND [-, 𝓥 ]) CBPV
    --
    -- we express its UMP as a vertical UMP:
    --   CBPV [-][-, UB ] ≅ (yoRec ≤)* (CBPV [-][-, B ])
    --
    -- Every vertical UMP is equivalent to a displayed one
    --
    --  CBPV [-][-, UB ] ≅[ id-iso(𝓥) ] (yoRec ≤)* (CBPV [-][-, B ])
    --
    -- *KEY STEP*
    -- Given any displayed UMP we can make a total presheaf on the total category
    --
    -- (∫ P Pᴰ) (x , xᴰ) = Σ[ p ∈ P x ] Pᴰ p xᴰ
    --
    -- And if Pᴰ is displayed representable then so is ∫ P Pᴰ(!)
    --
    -- In this case that means
    --    ∫ (KIND [-, 𝓥 ]) ((yoRec ≤)* CBPV [-][-, B])
    -- is represented by
    --    (𝓥 , UB)
    -- with universal element (𝓥≤𝓥 , force : CBPV [ 𝓥≤𝓥 ⋆ 𝓥≤𝓒 ][ UB , B ])
    --
    -- So the real question is...what is the displayed universal property of Uᴰ Bᴰ?
    --
    -- presumably it's over ∫ (KIND [-, 𝓥 ]) ((yoRec ≤)* CBPV [-][-, B ])
    -- Pᴰᴰ (𝓥≤𝓥 , M : CBPV [ _ ][ Γ , B ]) Γᴰ := Cᴰ [ _ , M ][ Γᴰ , Bᴰ ]
    --
    -- TODO: make this ergonomic
    [U]-UMP : ∀ (B : Ob 𝓒) → EqPsh.CartesianLiftUE CBPV (λ _ _ _ _ _ _ → Eq.refl) (λ {x} {y} f → Eq.refl) {x = 𝓥} _ B
    [U]-UMP B .v = [U] B
    [U]-UMP B .e = [force]
    [U]-UMP B .universal .isPshIsoEq.nIso (𝓥 , A , _) .fst = [thunk]
    [U]-UMP B .universal .isPshIsoEq.nIso (𝓥 , A , _) .snd .fst M = [Uβ] M
    [U]-UMP B .universal .isPshIsoEq.nIso (𝓥 , A , _) .snd .snd t = sym $ [Uη] t

    [U]-UMP' : ∀ (B : Ob 𝓒) → CartesianLift CBPV {x = 𝓥} _ B
    [U]-UMP' B = EqCartesianLift→CartesianLift _ CBPV B _ _
      (EqPsh.UEⱽ→Reprⱽ _ (λ {x} {y} f → Eq.refl) ([U]-UMP B))

    -- This is the base for the displayed Uᴰ UMP
    ∫[U]-Spec ∫[U]-Spec' : ∀ (B : Ob 𝓒) → Presheaf (∫C CBPV) _
    ∫[U]-Spec B = PresheafᴰNotation.∫ CBPV (KIND [-, 𝓥 ]) (reindPshᴰNatTrans (yoRec (KIND [-, 𝓒 ]) _) (CBPV [-][-, B ]))

    ∫[U]-Spec' B = improveF-hom (∫[U]-Spec B)
      λ { {𝓥 , Γ} {𝓥 , Γ'} (ı k'≤k , γ') .fst (ı pf , V) → _ , seqS γ' V
        ; {𝓥 , Γ} {𝓥 , Γ'} (ı k'≤k , γ') .snd → funExt λ (k≤𝓥 , M) →
          -- TODO: we should have a change-base for reindPshᴰNatTrans that we could use here
          change-base⁻ _ (YoB.reind-filler⁻ refl)
          -- change-base⁻ (λ _ → ı tt) (YoB.reind-filler⁻ refl)
        ; {𝓒 , Γ} {k , Γ'} (ı k'≤k , γ') .snd → funExt λ ()
        }
      where
        module YoB = PresheafᴰNotation CBPV _ (CBPV [-][-, B ])

    -- -- Where are the reinds coming from?
    -- -- do they go away if we use Path-based Element?
    ∫[U]-UMP : ∀ (B : Ob 𝓒) → UniversalElement (∫C CBPV) (∫[U]-Spec B)
    ∫[U]-UMP B = UniversalElementᴰNotation.∫ue CBPV (KIND [-, 𝓥 ]) _ (Representableⱽ→UniversalElementᴰ _ _ _ (selfUnivElt _ _)
      (_ , [U]-UMP' B .snd
        ⋆PshIso (invPshIso $ reindPshᴰNatTrans-tri _ _ _ _ (yoInd _ _ _ refl))))

    -- TODO: can we get this reind-free definition compositionally from U-UMP ?
    ∫[U]-UMP' : ∀ (B : Ob 𝓒) → UniversalElement (∫C CBPV) (∫[U]-Spec' B)
    ∫[U]-UMP' B .vertex = 𝓥 , [U] B
    ∫[U]-UMP' B .element = _ , [force]
    ∫[U]-UMP' B .universal (𝓥 , A) = isIsoToIsEquiv
      ( (λ (_ , M) → _ , [thunk] M)
      , (λ (_ , M) → ΣPathP (refl , [Uβ] M))
      , λ (_ , t) → ΣPathP (refl , (sym $ [Uη] t))
      )
    ∫[U]-UMP' B .universal (𝓒 , B') = isIsoToIsEquiv ((λ ()) , ((λ ()) , (λ ())))
    -- -- ∫[U]-UMP' B .UniversalElement.element = _ , [force]
    -- -- ∫[U]-UMP' B .UniversalElement.universal (_ , A) = isIsoToIsEquiv
    -- --   ( (λ (_ , M) → ? , ?)
    -- --     -- TODO: can we get this part reind-free ?
    -- --   , (λ _ → YoB.reind-filler⁻ refl ∙ (ΣPathP (refl , [Uβ] _)))
    -- --   , λ _ → {!!} ∙ ΣPathP (refl , (sym ([Uη] _)))
    -- --   )
    -- --   where
    -- --     module YoB = PresheafᴰNotation CBPV _ (CBPV [-][-, B ])
    -- --     module YoUB = PresheafᴰNotation CBPV _ (CBPV [-][-, [U] B ])

    -- -- -- [F]-UMP : ∀ (A : Ob 𝓥)
    -- -- --   → EqPsh.CartesianLiftUE (CBPV ^opᴰ) (λ _ _ _ _ _ _ → Eq.refl) (λ {x} {y} f → Eq.refl) {x = 𝓒} _ A
    -- -- -- [F]-UMP A .v = [F] A
    -- -- -- [F]-UMP A .e = [ret]
    -- -- -- [F]-UMP A .universal .isPshIsoEq.nIso (𝓒 , B , _) .fst = [bind]
    -- -- -- [F]-UMP A .universal .isPshIsoEq.nIso (𝓒 , B , _) .snd .fst M = [Fβ] M
    -- -- -- [F]-UMP A .universal .isPshIsoEq.nIso (𝓒 , B , _) .snd .snd S = sym $ [Fη] S

    -- -- -- -- So what is the *displayed* version of [U] and [F]?
    -- -- -- --
    -- -- -- -- Well the displayed version of [U] should be something such that
    -- -- -- -- if we take the displayed total category we get a [U] and the
    -- -- -- -- projection from ∫ᴰ Cᴰ → ∫ C preserves it strictly.
    -- -- -- --
    -- -- -- -- so I have some Bᴰ over (𝓒 , B) and I want a Uᴰ Bᴰ over (𝓥 , [U] B)
    -- -- -- --
    -- -- -- -- we should just take a cartesian lift of
    -- -- -- --
    -- -- -- --
    -- -- -- -- (𝓥 , [U] B) -[ _ , [force] ]→ (𝓒 , B)
    -- -- -- --
    -- -- -- -- This means it should be a "cartesian lift over a cartesian lift"
    -- -- -- -- and what is the *vertical* version?
    -- -- -- --
    -- -- -- -- The vertical version is certainly just a cartesian lift. It's
    -- -- -- -- preserved by reindexing no problemo.

    -- -- -- -- is this just a cartesian lift , but of what? Maybe
    -- -- -- --
    -- -- -- -- (∫ (KIND [-, 𝓥 ]) ((yoRec ≤)* CBPV [-][-, B ]))
    -- -- -- -- → (∫ (KIND [-, 𝓒 ]) (CBPV [-][-, B ]))
    -- -- -- module Elim
    -- -- --   (Cᴰ : Categoryᴰ (∫C CBPV) ℓᴰ ℓᴰ')
    -- -- --   where
    -- -- --   private
    -- -- --     module Cᴰ = Categoryᴰ Cᴰ

    -- -- --   Uᴰ-Spec : (B : Ob 𝓒)(Bᴰ : Cᴰ.ob[ _ , B ]) → Presheafᴰ (∫[U]-Spec B) Cᴰ ℓᴰ'
    -- -- --   Uᴰ-Spec B Bᴰ = reindPshᴰNatTrans
    -- -- --     (∫PshHomᴰ {α = yoRec _ _} idPshHom ⋆PshHom ∫Repr-iso CBPV .trans)
    -- -- --     (Cᴰ [-][-, Bᴰ ])

    -- -- --   module _
    -- -- --     (ı-Ob : ∀ {k} → (X : BaseTy k) → Cᴰ.ob[ _ , gen X ])
    -- -- --     (ı-U : ∀ (B : Ob 𝓒)(Bᴰ : Cᴰ.ob[ _ , B ])
    -- -- --       → UniversalElementᴰ Cᴰ (∫[U]-Spec B) (Uᴰ-Spec B Bᴰ) (∫[U]-UMP B))
    -- -- --     (ı-U' : ∀ (B : Ob 𝓒)(Bᴰ : Cᴰ.ob[ _ , B ])
    -- -- --       → UniversalElementᴰ Cᴰ (∫[U]-Spec B) (Uᴰ-Spec B Bᴰ) (∫[U]-UMP' B))
    -- -- --     where

    -- -- --     elim-F-obᴰ : ∀ Γ → Cᴰ.ob[ k , Γ ]
    -- -- --     elim-F-obᴰ (gen X) = ı-Ob X
    -- -- --     elim-F-obᴰ ([F] A) = {!!}
    -- -- --     elim-F-obᴰ ([U] B) = ı-U' B (elim-F-obᴰ B) .fst

    -- -- --     module _
    -- -- --       (ı-Fun : ∀ {k1 k2 Γ Δ}{k≤ : ≤Kind k1 k2} (M : Fun k≤ Γ Δ)
    -- -- --         → Cᴰ.Hom[ ı k≤ , gen M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ])
    -- -- --       where
    -- -- --       elim-F-homᴰ : (M : Tm k≤ Γ Δ) → Cᴰ.Hom[ ı k≤ , M ][ elim-F-obᴰ Γ , elim-F-obᴰ Δ ]
    -- -- --       elim-F-homᴰ (gen x) = ı-Fun x
    -- -- --       elim-F-homᴰ idS = Cᴰ.idᴰ
    -- -- --       elim-F-homᴰ (seqS M N) = elim-F-homᴰ M Cᴰ.⋆ᴰ elim-F-homᴰ N
    -- -- --       elim-F-homᴰ (IdLS M i) = {!!}
    -- -- --       elim-F-homᴰ (IdRS M i) = {!!}
    -- -- --       elim-F-homᴰ (AssocS M M₁ M₂ i) = {!!}
    -- -- --       elim-F-homᴰ (isSetTm M M₁ x y i i₁) = {!!}
    -- -- --       elim-F-homᴰ [ret] = {!!}
    -- -- --       elim-F-homᴰ ([bind] M) = {!!}
    -- -- --       elim-F-homᴰ ([Fβ] M i) = {!!}
    -- -- --       elim-F-homᴰ ([Fη] M i) = {!!}
    -- -- --       -- It works!!!
    -- -- --       elim-F-homᴰ ([force] {B}) = ı-U' B (elim-F-obᴰ B) .snd .fst
    -- -- --       elim-F-homᴰ ([thunk] M) = ı-U' _ (elim-F-obᴰ _) .snd .snd (𝓥 , _) (elim-F-obᴰ _)
    -- -- --                                  .isIsoOver.inv (ı tt , M) (elim-F-homᴰ M)
    -- -- --       -- something nasty I'm sure but it'll do.
    -- -- --       elim-F-homᴰ ([Uβ] M i) = {!!}
    -- -- --       elim-F-homᴰ ([Uη] M i) = {!!}

    -- -- --       elim : GlobalSection Cᴰ
    -- -- --       elim .F-obᴰ d = elim-F-obᴰ (d .snd)
    -- -- --       elim .F-homᴰ f = elim-F-homᴰ (f .snd)
    -- -- --       elim .F-idᴰ = refl
    -- -- --       elim .F-seqᴰ _ _ = refl
