{-
  Lambda-calculus like syntax

  Based on "category with display objects" variant of SCwF: a category with display objects is a category with a type of "display objects" which are a type of codes for objects of the category such that the category is closed under products with display objects.

  The idea is that the objects of the category are contexts and the display objects are types. Each type A can be interpreted as a singleton context x: A
  A terminal object represents the empty context.
  Product Γ × A is the context extension Γ ,x: A

  Terms and substitutions are unified into one sort, with the lambda terms being the substitutions with output x: A.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Lambda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Fiber
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
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD

private
  variable
    ℓ ℓ' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open Section
open PshIso
open PshHom
open UniversalElement

module _ (Base : Type ℓ) where
  data Ty : Type ℓ where
    ↑ : Base → Ty
    _[⇒]_ : Ty → Ty → Ty

  data Ctx : Type ℓ where
    [] : Ctx
    x: : Ty → Ctx
    _,x:_ : Ctx → Ty → Ctx

  module _ (Constant : Ty → Type ℓ') where
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
      _,,_ : ∀ {Δ Γ A} → Tm Δ Γ → Tm Δ (x: A) → Tm Δ (Γ ,x: A)
      wk : ∀ {Γ A} → Tm (Γ ,x: A) Γ
      var : ∀ {Γ A} → Tm (Γ ,x: A) (x: A)
      wkβ : ∀ {Δ Γ A}{γ : Tm Δ Γ}{M : Tm Δ (x: A)} → seqS (γ ,, M) wk ≡ γ
      varβ : ∀ {Δ Γ A}{γ : Tm Δ Γ}{M : Tm Δ (x: A)} → seqS (γ ,, M) var ≡ M
      ,,η : ∀ {Δ Γ A} (γ,M : Tm Δ (Γ ,x: A)) → γ,M ≡ (seqS γ,M wk ,, seqS γ,M var)

      -- function types
      [app] : ∀ {A B} → Tm (x: (A [⇒] B) ,x: A) (x: B)
      [λ]   : ∀ {Γ A B} → Tm (Γ ,x: A) (x: B) → Tm Γ (x: (A [⇒] B))
      ⇒η : ∀ {Γ A B} (M : Tm Γ (x: (A [⇒] B))) → M ≡ [λ] (seqS (seqS wk M ,, var) [app])
      ⇒β : ∀ {Γ A B} (M : Tm (Γ ,x: A) (x: B)) → seqS (seqS wk ([λ] M) ,, var) [app] ≡ M

    LAMBDA : Category ℓ (ℓ-max ℓ ℓ')
    LAMBDA .ob = Ctx
    LAMBDA .Hom[_,_] = Tm
    LAMBDA .id = idS
    LAMBDA ._⋆_ = seqS
    LAMBDA .⋆IdL = seqIdL
    LAMBDA .⋆IdR = seqIdR
    LAMBDA .⋆Assoc = seqAssoc
    LAMBDA .isSetHom = isSetTm

    TERMINALCTX : Terminal' LAMBDA
    TERMINALCTX .vertex = []
    TERMINALCTX .element = tt
    TERMINALCTX .universal Γ = isIsoToIsEquiv
      ((λ z → []) , ((λ _ → refl) , (λ γ⊤ → (sym $ []η _))))

    EXTENSION : ∀ A → BinProductsWith LAMBDA (x: A)
    EXTENSION A Γ .vertex = Γ ,x: A
    EXTENSION A Γ .element = wk , var
    EXTENSION A Γ .universal Δ = isIsoToIsEquiv
      ( (λ (γ , M) → γ ,, M)
      , (λ (γ , M) → ≡-× wkβ varβ)
      , λ γ,M → sym $ ,,η γ,M)

    EXPONENTIALS : ∀ A B → Exponential LAMBDA (x: A) (x: B) (EXTENSION A)
    EXPONENTIALS A B .vertex = x: (A [⇒] B)
    EXPONENTIALS A B .element = [app]
    EXPONENTIALS A B .universal Γ = isIsoToIsEquiv ( [λ] , ⇒β , (λ _ → sym $ ⇒η _))

    module _ (Cᴰ : Categoryᴰ LAMBDA ℓCᴰ ℓCᴰ')
      where
      private
        module Cᴰ = Fibers Cᴰ
      module _
        (termᴰ : Terminalᴰ Cᴰ TERMINALCTX)
        (bpᴰ : ∀ {A} (Aᴰ : Cᴰ.ob[ x: A ]) → BinProductsWithᴰ Cᴰ (EXTENSION A) Aᴰ)
        (⇒ᴰ : ∀ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ])
          → Exponentialᴰ Cᴰ (x: A , EXTENSION A) (Aᴰ , bpᴰ Aᴰ) Bᴰ (EXPONENTIALS A B))
        (ı : (A : Base) → Cᴰ.ob[ x: (↑ A) ]) where
        private
          module termᴰ = UniversalElementᴰNotation Cᴰ _ _ termᴰ
          module bpᴰ {Γ A}(Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Cᴰ.ob[ x: A ]) = BinProductᴰNotation Cᴰ (EXTENSION A Γ) (bpᴰ Aᴰ Γᴰ)
          module ⇒ᴰ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ]) = ExponentialᴰNotation (EXPONENTIALS A B) (⇒ᴰ Aᴰ Bᴰ)
          module EXTENSION {Γ : Ctx}{A : Ty} = BinProductNotation (EXTENSION A Γ)

        elimCtx : ∀ Γ → Cᴰ.ob[ Γ ]
        elimOb : ∀ A → Cᴰ.ob[ x: A ]
        elimCtx [] = termᴰ .fst
        elimCtx (x: A) = elimOb A
        elimCtx (Γ ,x: A) = bpᴰ (elimOb A) (elimCtx Γ) .fst

        elimOb (↑ X) = ı X
        elimOb (A [⇒] B) = ⇒ᴰ (elimOb A) (elimOb B) .fst

        elimTm : ∀ {Δ Γ} → (M : Tm Δ Γ) → Cᴰ.Hom[ M ][ elimCtx Δ , elimCtx Γ ]
        elimTm idS = Cᴰ.idᴰ
        elimTm (seqS M N) = elimTm M Cᴰ.⋆ᴰ elimTm N
        elimTm (seqAssoc M M₁ M₂ i) = Cᴰ.⋆Assocᴰ (elimTm M) (elimTm M₁) (elimTm M₂) i
        elimTm (seqIdL M i) = Cᴰ.⋆IdLᴰ (elimTm M) i
        elimTm (seqIdR M i) = Cᴰ.⋆IdRᴰ (elimTm M) i
        elimTm (isSetTm M N p q i j) = isSetHomᴰ' Cᴰ (elimTm M) (elimTm N) (cong elimTm p) (cong elimTm q) i j
        elimTm [] = termᴰ .snd .snd _ (elimCtx _) .isIsoOver.inv tt tt
        elimTm ([]η M i) = Cᴰ.rectify {e' = []η M} (termᴰ.ηᴰ (elimTm M)) i
        elimTm (γ ,, M) = bpᴰ.introᴰ _ _ (elimTm γ , elimTm M)
        elimTm wk = bpᴰ.πᴰ₁ _ _
        elimTm var = bpᴰ.πᴰ₂ _ _
        elimTm (wkβ i) = Cᴰ.rectify {e' = wkβ} (bpᴰ.×βᴰ₁ _ _ (elimTm _) (elimTm _)) i
        elimTm (varβ i) = Cᴰ.rectify {e' = varβ} (bpᴰ.×βᴰ₂ _ _ (elimTm _) (elimTm _)) i
        elimTm (,,η M i) = Cᴰ.rectify {e' = ,,η M} (bpᴰ.×ηᴰ (elimCtx _) (elimOb _) (elimTm M)) i
        elimTm [app] = ⇒ᴰ.appᴰ (elimOb _) (elimOb _)
        elimTm ([λ] M) = ⇒ᴰ.λᴰ _ _ (elimTm M)

        elimTm (⇒β M i) = Cᴰ.rectify {e' = ⇒β M} (Cᴰ.≡out $ ⇒ᴰ.⇒βᴰ _ _ (elimTm M)) i
        elimTm (⇒η M i) = Cᴰ.rectify {e' = ⇒η M} (Cᴰ.≡out $ ⇒ᴰ.⇒ηᴰ _ _ (elimTm M)) i

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elimCtx
        elim .F-homᴰ = elimTm
        elim .F-idᴰ = refl
        elim .F-seqᴰ = λ _ _ → refl
