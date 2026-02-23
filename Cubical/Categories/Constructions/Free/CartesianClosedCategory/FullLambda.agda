{-
  Lambda-calculus like syntax

  Based on "category with display objects" variant of SCwF: a category with display objects is a category with a type of "display objects" which are a type of codes for objects of the category such that the category is closed under products with display objects.

  The idea is that the objects of the category are contexts and the display objects are types. Each type A can be interpreted as a singleton context x: A
  A terminal object represents the empty context.
  Product Γ × A is the context extension Γ ,x: A

  Terms and substitutions are unified into one sort, with the lambda terms being the substitutions with output x: A.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianClosedCategory.FullLambda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv.Dependent
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.HLevels.More

import Cubical.Data.Equality as Eq
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.HITs.SetQuotients as Quo hiding (elim)

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
open import Cubical.Categories.Displayed.Constructions.Reindex
open import Cubical.Categories.Displayed.More
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Representable
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD

private
  variable
    ℓ ℓ' ℓ'' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open Section
open PshIso
open PshHom
open UniversalElement

module Lambda⇒Ty (Base : Type ℓ) where
  data Ty : Type ℓ where
    ↑ : Base → Ty
    ⊥ ⊤ : Ty
    _[⇒]_ _[+]_ _[×]_ : Ty → Ty → Ty

  data Ctx : Type ℓ where
    [] : Ctx
    x: : Ty → Ctx
    _,x:_ : Ctx → Ty → Ctx

module Lambda⇒
       (Base : Type ℓ)
       (Constant : Lambda⇒Ty.Ty Base → Type ℓ')
       where
  open Lambda⇒Ty Base public
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

    -- ⊤
    [[]] : ∀ {Γ} → Tm Γ (x: ⊤)
    ⊤η : ∀ {Γ} (M : Tm Γ (x: ⊤)) → M ≡ [[]]

    -- product types
    [π₁] : ∀ {A B} → Tm (x: (A [×] B)) (x: A)
    [π₂] : ∀ {A B} → Tm (x: (A [×] B)) (x: B)
    _[,]_ : ∀ {Γ A B} → Tm Γ (x: A) → Tm Γ (x: B) → Tm Γ (x: (A [×] B))
    [×η] : ∀ {Γ A B} (M : Tm Γ (x: (A [×] B)))
      → M ≡ (seqS M [π₁] [,] seqS M [π₂])
    [×β₁] : ∀ {Γ A B} (M₁ : Tm Γ (x: A)) (M₂ : Tm Γ (x: B))
      → seqS (M₁ [,] M₂) [π₁] ≡ M₁
    [×β₂] : ∀ {Γ A B} (M₁ : Tm Γ (x: A)) (M₂ : Tm Γ (x: B))
      → seqS (M₁ [,] M₂) [π₂] ≡ M₂

    -- ⊥
    [case⊥] : ∀ {Γ B} → Tm (Γ ,x: ⊥) B
    [⊥η] : ∀ {Γ B} → (M : Tm (Γ ,x: ⊥) B) → M ≡ [case⊥]

    -- +
    [σ₁] : ∀ {A₁ A₂} → Tm (x: A₁) (x: (A₁ [+] A₂))
    [σ₂] : ∀ {A₁ A₂} → Tm (x: A₂) (x: (A₁ [+] A₂))
    [case+] : ∀ {Γ A₁ A₂ B}
      → Tm (Γ ,x: A₁) B
      → Tm (Γ ,x: A₂) B
      → Tm (Γ ,x: (A₁ [+] A₂)) B
    [+β₁] : ∀ {Γ A₁ A₂ B}
      → (M₁ : Tm (Γ ,x: A₁) B) (M₂ : Tm (Γ ,x: A₂) B)
      → seqS (wk ,x= seqS var [σ₁]) ([case+] M₁ M₂) ≡ M₁
    [+β₂] : ∀ {Γ A₁ A₂ B}
      → (M₁ : Tm (Γ ,x: A₁) B) (M₂ : Tm (Γ ,x: A₂) B)
      → seqS (wk ,x= seqS var [σ₂]) ([case+] M₁ M₂) ≡ M₂
    [+η] : ∀ {Γ A₁ A₂ B}
      → (M : Tm (Γ ,x: (A₁ [+] A₂)) B)
      → M ≡ [case+] (seqS (wk ,x= seqS var [σ₁]) M) (seqS (wk ,x= seqS var [σ₂]) M)

    -- constants
    gen : ∀ {A} (f : Constant A) → Tm [] (x: A)

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
    ( (λ (γ , M) → γ ,x= M)
    , (λ (γ , M) → ≡-× wkβ varβ)
    , λ γ,M → sym $ ,x=η γ,M)

  EXPONENTIALS : ∀ A B → Exponential LAMBDA (x: A) (x: B) (EXTENSION A)
  EXPONENTIALS A B .vertex = x: (A [⇒] B)
  EXPONENTIALS A B .element = [app]
  EXPONENTIALS A B .universal Γ = isIsoToIsEquiv ( [λ] , ⇒β , (λ _ → sym $ ⇒η _))
