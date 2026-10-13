-- Negative fragment of STLC: 1, × , ⇒

{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Free.Lambda.Negative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More
open import Cubical.Foundations.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.SetQuotients as Quo hiding (elim)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.Fiber
open import Cubical.Categories.Exponentials.Small
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Presheaf.Constructions.BinProduct
open import Cubical.Categories.Presheaf.Constructions.Exponential
open import Cubical.Categories.Presheaf.Constructions.Reindex
open import Cubical.Categories.Presheaf.Constructions.Unit
open import Cubical.Categories.Presheaf.More
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Representable
open import Cubical.Categories.Presheaf.Representable.More

open import Cubical.Categories.Limits.Cartesian.Base
open import Cubical.Categories.Limits.BinProduct.More
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Limits.CartesianClosed.Base

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Base
open import Cubical.Categories.Displayed.Instances.Reindex.Cartesian
open import Cubical.Categories.Displayed.Instances.Reindex.CartesianClosed
open import Cubical.Categories.Displayed.Instances.Reindex.Exponential
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
open import Cubical.Categories.Displayed.Instances.Reindex.Fibration
open import Cubical.Categories.Displayed.Instances.Reindex.UniversalQuantifier
open import Cubical.Categories.Displayed.Limits.CartesianV'
open import Cubical.Categories.Displayed.Limits.CartesianClosedV
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialV->D

private
  variable
    ℓ ℓ' ℓ'' ℓD ℓD' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open Section
open PshIso
open PshHom
open UniversalElement

module Lambda1×⇒Ty (Base : Type ℓ) where
  data Ty : Type ℓ where
    ↑ : Base → Ty
    [1] : Ty
    _[⇒]_ _[×]_ : Ty → Ty → Ty

  data Ctx : Type ℓ where
    [] : Ctx
    x: : Ty → Ctx
    _,x:_ : Ctx → Ty → Ctx

module Lambda1×⇒
       (Base : Type ℓ)
       (Constant : Lambda1×⇒Ty.Ty Base → Type ℓ')
       where
  open Lambda1×⇒Ty Base public
  data Tm : (Δ Γ : Ctx) → Type (ℓ-max ℓ ℓ') where
    idS  : ∀ {Γ} → Tm Γ Γ
    seqS : ∀ {Γ Δ Θ} (δ : Tm Γ Δ) (θ : Tm Δ Θ) → Tm Γ Θ
    seqAssoc : ∀ {Γ Δ Θ H} (γ : Tm H Γ)(δ : Tm Γ Δ)(θ : Tm Δ Θ)
      → seqS (seqS γ δ) θ ≡ seqS γ (seqS δ θ)
    seqIdL :  ∀ {Γ Δ} (δ : Tm Γ Δ)
      → seqS idS δ ≡ δ
    seqIdR :  ∀ {Γ Δ} (δ : Tm Γ Δ)
      → seqS δ idS ≡ δ
    isSetTm : ∀ {Γ Δ} → isSet (Tm Γ Δ)

    [] : ∀ {Γ} → Tm Γ []
    []η : ∀ {Γ} (δ : Tm Γ []) → δ ≡ []

    -- closed under products by types
    _,x=_ : ∀ {Δ Γ A} → Tm Δ Γ → Tm Δ (x: A) → Tm Δ (Γ ,x: A)
    wk : ∀ {Γ A} → Tm (Γ ,x: A) Γ
    var : ∀ {Γ A} → Tm (Γ ,x: A) (x: A)
    wkβ : ∀ {Δ Γ A}{γ : Tm Δ Γ}{M : Tm Δ (x: A)} → seqS (γ ,x= M) wk ≡ γ
    varβ : ∀ {Δ Γ A}{γ : Tm Δ Γ}{M : Tm Δ (x: A)} → seqS (γ ,x= M) var ≡ M
    ,x=η : ∀ {Δ Γ A} (γ,M : Tm Δ (Γ ,x: A)) → γ,M ≡ (seqS γ,M wk ,x= seqS γ,M var)

    -- function types
    [app] : ∀ {A B} → Tm (x: (A [⇒] B) ,x: A) (x: B)
    [λ]   : ∀ {Γ A B} → Tm (Γ ,x: A) (x: B) → Tm Γ (x: (A [⇒] B))
    ⇒η : ∀ {Γ A B} (M : Tm Γ (x: (A [⇒] B))) → M ≡ [λ] (seqS (seqS wk M ,x= var) [app])
    ⇒β : ∀ {Γ A B} (M : Tm (Γ ,x: A) (x: B)) → seqS (seqS wk ([λ] M) ,x= var) [app] ≡ M

    -- unit type
    [[]] : ∀ {Γ} → Tm Γ (x: [1])
    1η : ∀ {Γ} (M : Tm Γ (x: [1])) → M ≡ [[]]

    -- product type
    [⟨_,_⟩] : ∀ {Γ A₁ A₂} (M₁ : Tm Γ (x: A₁))(M₂ : Tm Γ (x: A₂)) → Tm Γ (x: (A₁ [×] A₂))
    [π₁] : ∀ {A₁ A₂} → Tm (x: (A₁ [×] A₂)) (x: A₁)
    [π₂] : ∀ {A₁ A₂} → Tm (x: (A₁ [×] A₂)) (x: A₂)
    ×η : ∀ {Γ A₁ A₂} (M : Tm Γ (x: (A₁ [×] A₂))) → M ≡ [⟨ seqS M [π₁] , seqS M [π₂] ⟩]
    ×β₁ : ∀ {Γ A₁ A₂} (M₁ : Tm Γ (x: A₁))(M₂ : Tm Γ (x: A₂)) → seqS [⟨ M₁ , M₂ ⟩] [π₁] ≡ M₁
    ×β₂ : ∀ {Γ A₁ A₂} (M₁ : Tm Γ (x: A₁))(M₂ : Tm Γ (x: A₂)) → seqS [⟨ M₁ , M₂ ⟩] [π₂] ≡ M₂

    -- constants
    gen : ∀ {A} (f : Constant A) → Tm [] (x: A)

  [APP] : ∀ {Γ A B} → Tm Γ (x: (A [⇒] B)) → Tm Γ (x: A) → Tm Γ (x: B)
  [APP] M N = seqS (M ,x= N) [app]

  LAMBDA : Category ℓ (ℓ-max ℓ ℓ')
  LAMBDA .ob = Ctx
  LAMBDA .Hom[_,_] = Tm
  LAMBDA .id = idS
  LAMBDA ._⋆_ = seqS
  LAMBDA .⋆IdL = seqIdL
  LAMBDA .⋆IdR = seqIdR
  LAMBDA .⋆Assoc = seqAssoc
  LAMBDA .isSetHom = isSetTm
  module LAMBDA = Category LAMBDA

  TERMINALCTX : Terminal' LAMBDA
  TERMINALCTX .vertex = []
  TERMINALCTX .element = tt
  TERMINALCTX .universal Γ = isIsoToIsEquiv
    ((λ z → []) , ((λ _ → refl) , (λ γ⊤ → (sym $ []η _))))

  EXTENSION : ∀ A → BinProductsWith LAMBDA (x: A)
  EXTENSION A Γ .vertex = Γ ,x: A
  EXTENSION A Γ .element = wk , var
  EXTENSION A Γ .universal Δ = isIsoToIsEquiv
    ( (λ (γ , M) → γ ,x= M)
    , (λ (γ , M) → ≡-× wkβ varβ)
    , λ γ,M → sym $ ,x=η γ,M)

  EXPONENTIALS : ∀ A B → Exponential LAMBDA (x: A) (x: B) (EXTENSION A)
  EXPONENTIALS A B .vertex = x: (A [⇒] B)
  EXPONENTIALS A B .element = [app]
  EXPONENTIALS A B .universal Γ = isIsoToIsEquiv ( [λ] , ⇒β , (λ _ → sym $ ⇒η _))

  TERMINALTY : Terminal' LAMBDA
  TERMINALTY .vertex = x: [1]
  TERMINALTY .element = tt
  TERMINALTY .universal Γ = isIsoToIsEquiv
    ( (λ z → [[]])
    , (λ _ → refl)
    , (λ M → sym (1η M)))

  PRODTY : ∀ A B → BinProduct LAMBDA ((x: A) , (x: B))
  PRODTY A B .vertex = x: (A [×] B)
  PRODTY A B .element = [π₁] , [π₂]
  PRODTY A B .universal Γ = isIsoToIsEquiv (
    (λ M1,M2 → [⟨ M1,M2 .fst , M1,M2 .snd ⟩])
    , (λ M1,M2 → (≡-× ((×β₁ (M1,M2 .fst) (M1,M2 .snd))) ((×β₂ (M1,M2 .fst) (M1,M2 .snd)))))
    , (λ M → sym (×η M)))

  module _ (Cᴰ : Categoryᴰ LAMBDA ℓCᴰ ℓCᴰ')
    where
    private
      module Cᴰ = Fibers Cᴰ
    module _
      (termᴰ : Terminalᴰ Cᴰ TERMINALCTX)
      (bpᴰ : ∀ {A} (Aᴰ : Cᴰ.ob[ x: A ]) → BinProductsWithᴰ Cᴰ (EXTENSION A) Aᴰ)
      (⇒ᴰ : ∀ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ])
        → Exponentialᴰ Cᴰ (x: A , EXTENSION A) (Aᴰ , bpᴰ Aᴰ) Bᴰ (EXPONENTIALS A B))
      (1ᴰ : Terminalᴰ Cᴰ TERMINALTY)
      (bp-tyᴰ : ∀ {A B}(Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ]) → BinProductᴰ Cᴰ (PRODTY A B) Aᴰ Bᴰ)
      (ı : (A : Base) → Cᴰ.ob[ x: (↑ A) ]) where
      private
        module termᴰ = UniversalElementᴰNotation Cᴰ _ _ termᴰ
        module bpᴰ {Γ A}(Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Cᴰ.ob[ x: A ]) = BinProductᴰNotation Cᴰ (EXTENSION A Γ) (bpᴰ Aᴰ Γᴰ)
        module 1ᴰ = UniversalElementᴰNotation Cᴰ _ _ 1ᴰ
        module bp-tyᴰ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ]) = BinProductᴰNotation Cᴰ (PRODTY A B) (bp-tyᴰ Aᴰ Bᴰ)
        module ⇒ᴰ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ]) = ExponentialᴰNotation (EXPONENTIALS A B) (⇒ᴰ Aᴰ Bᴰ)
        module EXTENSION {Γ : Ctx}{A : Ty} = BinProductNotation (EXTENSION A Γ)

      elimCtx : ∀ Γ → Cᴰ.ob[ Γ ]
      elimOb : ∀ A → Cᴰ.ob[ x: A ]
      elimCtx [] = termᴰ .fst
      elimCtx (x: A) = elimOb A
      elimCtx (Γ ,x: A) = bpᴰ (elimOb A) (elimCtx Γ) .fst

      elimOb (↑ X) = ı X
      elimOb (A [⇒] B) = ⇒ᴰ (elimOb A) (elimOb B) .fst
      elimOb [1] = 1ᴰ .fst
      elimOb (A₁ [×] A₂) = bp-tyᴰ (elimOb A₁) (elimOb A₂) .fst

      module _ (ı-const : ∀ {A} (f : Constant A) → Cᴰ.Hom[ gen f ][ elimCtx [] , elimCtx (x: A) ]) where
        elimTm : ∀ {Δ Γ} → (M : Tm Δ Γ) → Cᴰ.Hom[ M ][ elimCtx Δ , elimCtx Γ ]
        elimTm idS = Cᴰ.idᴰ
        elimTm (seqS M N) = elimTm M Cᴰ.⋆ᴰ elimTm N
        elimTm (seqAssoc M M₁ M₂ i) = Cᴰ.⋆Assocᴰ (elimTm M) (elimTm M₁) (elimTm M₂) i
        elimTm (seqIdL M i) = Cᴰ.⋆IdLᴰ (elimTm M) i
        elimTm (seqIdR M i) = Cᴰ.⋆IdRᴰ (elimTm M) i
        elimTm (isSetTm M N p q i j) = isSetHomᴰ' Cᴰ (elimTm M) (elimTm N) (cong elimTm p) (cong elimTm q) i j
        elimTm [] = termᴰ .snd .snd _ (elimCtx _) .isIsoOver.inv tt tt
        elimTm ([]η M i) = Cᴰ.rectify {e' = []η M} (termᴰ.ηᴰ (elimTm M)) i
        elimTm (γ ,x= M) = bpᴰ.introᴰ _ _ (elimTm γ , elimTm M)
        elimTm wk = bpᴰ.πᴰ₁ _ _
        elimTm var = bpᴰ.πᴰ₂ _ _
        elimTm (wkβ i) = Cᴰ.rectify {e' = wkβ} (bpᴰ.×βᴰ₁ _ _ (elimTm _) (elimTm _)) i
        elimTm (varβ i) = Cᴰ.rectify {e' = varβ} (bpᴰ.×βᴰ₂ _ _ (elimTm _) (elimTm _)) i
        elimTm (,x=η M i) = Cᴰ.rectify {e' = ,x=η M} (bpᴰ.×ηᴰ (elimCtx _) (elimOb _) (elimTm M)) i
        elimTm [app] = ⇒ᴰ.appᴰ (elimOb _) (elimOb _)
        elimTm ([λ] M) = ⇒ᴰ.λᴰ _ _ (elimTm M)
        elimTm (⇒β M i) = Cᴰ.rectify {e' = ⇒β M} (Cᴰ.≡out $ ⇒ᴰ.⇒βᴰ _ _ (elimTm M)) i
        elimTm (⇒η M i) = Cᴰ.rectify {e' = ⇒η M} (Cᴰ.≡out $ ⇒ᴰ.⇒ηᴰ _ _ (elimTm M)) i
        elimTm (gen f) = ı-const f
        elimTm [[]] = 1ᴰ .snd .snd _ (elimCtx _) .isIsoOver.inv _ _
        elimTm (1η M i) = Cᴰ.rectify {e' = 1η M} (1ᴰ.ηᴰ (elimTm M)) i
        elimTm [⟨ M₁ , M₂ ⟩] = bp-tyᴰ.introᴰ _ _ ((elimTm M₁) , (elimTm M₂))
        elimTm [π₁] = bp-tyᴰ.πᴰ₁ _ _
        elimTm [π₂] = bp-tyᴰ.πᴰ₂ _ _
        elimTm (×η M i) = Cᴰ.rectify {e' = ×η M} (bp-tyᴰ.×ηᴰ (elimCtx _) (elimOb _) (elimTm M)) i
        elimTm (×β₁ M₁ M₂ i) = Cᴰ.rectify {e' = ×β₁ _ _} (bp-tyᴰ.×βᴰ₁ _ _ (elimTm _) (elimTm _)) i
        elimTm (×β₂ M₁ M₂ i) = Cᴰ.rectify {e' = ×β₂ _ _} (bp-tyᴰ.×βᴰ₂ _ _ (elimTm _) (elimTm _)) i

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elimCtx
        elim .F-homᴰ = elimTm
        elim .F-idᴰ = refl
        elim .F-seqᴰ = λ _ _ → refl

  module _ (D : CartesianCategory ℓD ℓD')
    (F : Functor LAMBDA (D .CartesianCategory.C))
    (F-× : ∀ A → preservesProvidedBinProductsWith F (EXTENSION A))
    (CCCⱽ : CartesianClosedCategoryⱽ D ℓCᴰ ℓCᴰ')
    where
    private
      module CCCⱽ = CartesianClosedCategoryⱽ CCCⱽ
      F*Termᴰ : Terminalᴰ (reindex CCCⱽ.Cᴰ F) TERMINALCTX
      F*Termᴰ = (Terminalⱽ→ᴰ (reindex CCCⱽ.Cᴰ F) _ (TerminalsⱽReindex F CCCⱽ.termⱽ []))

      F*BPᴰ : {A : Ty} (Aᴰ : CCCⱽ.Cᴰ.ob[ F-ob F (x: A) ]) → BinProductsWithᴰ (reindex CCCⱽ.Cᴰ F) (EXTENSION A) Aᴰ
      F*BPᴰ {A = A} Aᴰ Bᴰ = BinProductⱽ+π*→ᴰ (reindex CCCⱽ.Cᴰ F) _ Bᴰ Aᴰ
        (reindexCartesianLift CCCⱽ.Cᴰ F wk  Bᴰ (CCCⱽ.cartesianLifts Bᴰ _ (F-hom F wk)))
        (reindexCartesianLift CCCⱽ.Cᴰ F var Aᴰ (CCCⱽ.cartesianLifts Aᴰ _ (F-hom F var)))
        (reindexBinProductⱽ F _ _ (CCCⱽ.bpⱽ _ _))

      F*1ᴰ : Terminalᴰ (reindex CCCⱽ.Cᴰ F) TERMINALTY
      F*1ᴰ = (Terminalⱽ→ᴰ (reindex CCCⱽ.Cᴰ F) _ (TerminalsⱽReindex F CCCⱽ.termⱽ (x: [1])))

      F*×ᴰ : ∀ {A B} Aᴰ Bᴰ → BinProductᴰ (reindex CCCⱽ.Cᴰ F) (PRODTY A B) Aᴰ Bᴰ
      F*×ᴰ {A} {B} Aᴰ Bᴰ = BinProductⱽ+π*→ᴰ (reindex CCCⱽ.Cᴰ F) _ Aᴰ Bᴰ
        (reindexCartesianLift CCCⱽ.Cᴰ F [π₁] Aᴰ (CCCⱽ.cartesianLifts Aᴰ (F-ob F (x: (A [×] B))) (F-hom F [π₁])))
        (reindexCartesianLift CCCⱽ.Cᴰ F [π₂] Bᴰ (CCCⱽ.cartesianLifts Bᴰ (F-ob F (x: (A [×] B))) (F-hom F [π₂])))
        (reindexBinProductⱽ F _ _ (CCCⱽ.bpⱽ _ _))

      F*Expᴰ : {A B : Ty} (Aᴰ : CCCⱽ.Cᴰ.ob[ F-ob F (x: A) ])
        (Bᴰ : CCCⱽ.Cᴰ.ob[ F-ob F (x: B) ]) →
        Exponentialᴰ (reindex CCCⱽ.Cᴰ F) (x: A , EXTENSION A)
        (Aᴰ , F*BPᴰ Aᴰ) Bᴰ (EXPONENTIALS A B)
      F*Expᴰ {A}{B} Aᴰ Bᴰ = ∀+Expⱽ+lifts⇒Expᴰ
        (reindexCartesianLift CCCⱽ.Cᴰ _ _ _ (CCCⱽ.cartesianLifts _ _ _))
        (isLRⱽObᴰReindex _ _ (CCCⱽ.lrⱽ _))
        (reindexCartesianLift CCCⱽ.Cᴰ _ _ _ (CCCⱽ.cartesianLifts _ _ _))
        (reindexExponentialⱽ _ _ _ (CCCⱽ.expⱽ _ _))
        (λ _ _ → reindexCartesianLift CCCⱽ.Cᴰ _ _ _ (CCCⱽ.cartesianLifts _ _ _))
        (reflectsUniversalQuantifiers _ _ CCCⱽ.cartesianLifts (EXTENSION A) (λ c → D .CartesianCategory.bp (c , F-ob F (x: A))) (F-× A) _ (CCCⱽ.forallⱽ _))

    elimLocal :
      (ıOb : (A : Base) → CCCⱽ.Cᴰ.ob[ F  .F-ob (x: (↑ A)) ])
      → ({A : Ty} (f : Constant A) →
        CCCⱽ.Cᴰ.Hom[ F-hom F (gen f) ][ F*Termᴰ .fst ,
        elimOb (reindex CCCⱽ.Cᴰ F) F*Termᴰ F*BPᴰ F*Expᴰ F*1ᴰ F*×ᴰ ıOb A ])
      → Section F CCCⱽ.Cᴰ
    elimLocal ıOb ıHom = GlobalSectionReindex→Section _ _
      (elim (reindex CCCⱽ.Cᴰ F) F*Termᴰ F*BPᴰ F*Expᴰ F*1ᴰ F*×ᴰ ıOb ıHom)
