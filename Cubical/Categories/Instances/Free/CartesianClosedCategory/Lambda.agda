{-
  Lambda-calculus like syntax

  Based on "category with display objects" variant of SCwF: a category with display objects is a category with a type of "display objects" which are a type of codes for objects of the category such that the category is closed under products with display objects.

  The idea is that the objects of the category are contexts and the display objects are types. Each type A can be interpreted as a singleton context x: A
  A terminal object represents the empty context.
  Product Γ × A is the context extension Γ ,x: A

  Terms and substitutions are unified into one sort, with the lambda terms being the substitutions with output x: A.

-}
{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Instances.Free.CartesianClosedCategory.Lambda where

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
open import Cubical.Categories.Displayed.Instances.Reindex.Eq
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
    _[⇒]_ : Ty → Ty → Ty

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

        elim : GlobalSection Cᴰ
        elim .F-obᴰ = elimCtx
        elim .F-homᴰ = elimTm
        elim .F-idᴰ = refl
        elim .F-seqᴰ = λ _ _ → refl

module Lambda⇒/≈
  (Base : Type ℓ)
  (Constant : Lambda⇒Ty.Ty Base → Type ℓ')
  where
  open Lambda⇒ Base Constant public
  module _ (Axiom : ∀ {A} (M N : Tm [] (x: A)) → Type ℓ'') where
    data _≈_ : ∀ {Γ A} (M N : Tm Γ A) → Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
      refl≈ : ∀ {Δ Γ} (γ : Tm Δ Γ) → γ ≈ γ
      ⋆≈ : ∀ {Δ Γ A} {γ γ' : Tm Δ Γ}{M M' : Tm Γ A}
        → γ ≈ γ' → M ≈ M' → seqS γ M ≈ seqS γ' M'
      [λ]≈ : ∀ {Γ A B} {M M' : Tm (Γ ,x: A) (x: B)}
        → M ≈ M' → [λ] M ≈ [λ] M'
      ,x=≈ : ∀ {Δ Γ A}{γ γ' : Tm Δ Γ}{M M' : Tm Δ (x: A)}
        → γ ≈ γ' → M ≈ M'
        → (γ ,x= M) ≈ (γ' ,x= M')
      ax : ∀ {A M N} → Axiom {A} M N → M ≈ N

    LAMBDA/≈ : Category ℓ (ℓ-max (ℓ-max ℓ ℓ') ℓ'')
    LAMBDA/≈ .ob = Ctx
    LAMBDA/≈ .Hom[_,_] Δ Γ = Tm Δ Γ / _≈_
    LAMBDA/≈ .id = [ idS ]
    LAMBDA/≈ ._⋆_ = rec2 squash/ (λ γ M → [ seqS γ M ])
      (λ γ γ' M γ≈γ' → eq/ (seqS γ M) (seqS γ' M) (⋆≈ γ≈γ' (refl≈ M)))
      λ γ M M' M≈M' → eq/ _ _ (⋆≈ (refl≈ γ) M≈M')
    LAMBDA/≈ .⋆IdL = elimProp (λ _ → squash/ _ _) (λ M → cong [_] (seqIdL M))
    LAMBDA/≈ .⋆IdR = elimProp (λ _ → squash/ _ _) (λ M → cong [_] (seqIdR M))
    LAMBDA/≈ .⋆Assoc = elimProp3 (λ _ _ _ → squash/ _ _) (λ δ γ M → cong [_] (seqAssoc δ γ M))
    LAMBDA/≈ .isSetHom = squash/

    TERMINAL≈ : Terminal' LAMBDA/≈
    TERMINAL≈ .vertex = []
    TERMINAL≈ .element = tt
    TERMINAL≈ .universal Γ = isIsoToIsEquiv
      ( (λ z → [ [] ])
      , ((λ _ → refl)
      , Quo.elimProp (λ _ → squash/ _ _) λ M → cong [_] (sym ([]η M))))

    EXTENSION≈ : ∀ A → BinProductsWith LAMBDA/≈ (x: A)
    EXTENSION≈ A Γ .vertex = Γ ,x: A
    EXTENSION≈ A Γ .element = [ wk ] , [ var ]
    EXTENSION≈ A Γ .universal Δ = isIsoToIsEquiv
      ( (uncurry (rec2 squash/ (λ γ M → [ γ ,x= M ])
                 (λ γ γ' M γ≈γ' → eq/ _ _ (,x=≈ γ≈γ' (refl≈ M)))
                 λ γ M M' M≈M' → eq/ _ _ (,x=≈ (refl≈ γ) M≈M')))
      , uncurry (elimProp2 (λ _ _ → isSet× squash/ squash/ _ _) λ γ M → ≡-× (cong [_] wkβ) (cong [_] varβ))
      , elimProp (λ _ → squash/ _ _) (λ γ,x=M → sym (cong [_] (,x=η γ,x=M)))
      )

    EXPONENTIALS≈ : ∀ A B → Exponential LAMBDA/≈ (x: A) (x: B) (EXTENSION≈ A)
    EXPONENTIALS≈ A B .vertex = x: (A [⇒] B)
    EXPONENTIALS≈ A B .element = [ [app] ]
    EXPONENTIALS≈ A B .universal Γ = isIsoToIsEquiv
      ( (rec squash/ (λ M → [ [λ] M ]) λ M M' M≈M' → eq/ _ _ ([λ]≈ M≈M'))
      , elimProp (λ _ → squash/ _ _) (λ M → cong [_] (⇒β M))
      , elimProp (λ _ → squash/ _ _) (λ M → cong [_] (sym (⇒η M))))

    QuoFunctor : Functor LAMBDA LAMBDA/≈
    QuoFunctor .F-ob Γ = Γ
    QuoFunctor .F-hom = [_]
    QuoFunctor .F-id = refl
    QuoFunctor .F-seq δ γ = refl

    module _ (Cᴰ : Categoryᴰ LAMBDA/≈ ℓCᴰ ℓCᴰ')
      where
      private
        module Cᴰ = Fibers Cᴰ
      module _
        (termᴰ : Terminalᴰ Cᴰ TERMINAL≈)
        (bpᴰ : ∀ {A} (Aᴰ : Cᴰ.ob[ x: A ]) → BinProductsWithᴰ Cᴰ (EXTENSION≈ A) Aᴰ)
        (⇒ᴰ : ∀ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ])
          → Exponentialᴰ Cᴰ (x: A , EXTENSION≈ A) (Aᴰ , bpᴰ Aᴰ) Bᴰ (EXPONENTIALS≈ A B))
        (ı : (A : Base) → Cᴰ.ob[ x: (↑ A) ]) where
        private
          module termᴰ = UniversalElementᴰNotation Cᴰ _ _ termᴰ
          module bpᴰ {Γ A}(Γᴰ : Cᴰ.ob[ Γ ])(Aᴰ : Cᴰ.ob[ x: A ]) = BinProductᴰNotation Cᴰ (EXTENSION≈ A Γ) (bpᴰ Aᴰ Γᴰ)
          module ⇒ᴰ {A B} (Aᴰ : Cᴰ.ob[ x: A ])(Bᴰ : Cᴰ.ob[ x: B ]) = ExponentialᴰNotation (EXPONENTIALS≈ A B) (⇒ᴰ Aᴰ Bᴰ)
          module EXTENSION {Γ : Ctx}{A : Ty} = BinProductNotation (EXTENSION A Γ)

          module reindexCᴰ = EqReindexProperties Cᴰ QuoFunctor Eq.refl (λ _ _ → Eq.refl)
          Quo*Cᴰ = reindexCᴰ.reindex
          module Quo*Cᴰ = Fibers Quo*Cᴰ
        -- TODO: because QuoFunctor strictly preserves extension and exponentials,
        -- the TERMINALᴰ, BPᴰ and EXPᴰ can all be reindexed to be over LAMBDA, and we can thus define an eliminator into Quo*Cᴰ
          Quo*termᴰ : Terminalᴰ Quo*Cᴰ TERMINALCTX
          Quo*termᴰ = reindexCᴰ.reflectsTerminalᴰ (TERMINAL≈ .universal) termᴰ


          -- 
          Quo*bpᴰ : {A : Ty} (Aᴰ : Quo*Cᴰ.ob[ x: A ]) → BinProductsWithᴰ Quo*Cᴰ (EXTENSION A) Aᴰ
          Quo*bpᴰ {A} Aᴰ {B} Bᴰ = reindexCᴰ.reflectsBPᴰ (EXTENSION A B) (EXTENSION≈ A B .universal) (bpᴰ Aᴰ Bᴰ)

          Quo*⇒ᴰ : {A B : Ty} (Aᴰ : Quo*Cᴰ.ob[ x: A ]) (Bᴰ : Quo*Cᴰ.ob[ x: B ])
            → Exponentialᴰ Quo*Cᴰ (x: A , EXTENSION A) (Aᴰ , Quo*bpᴰ Aᴰ) Bᴰ (EXPONENTIALS A B)
          Quo*⇒ᴰ {A} {B} Aᴰ Bᴰ .fst = ⇒ᴰ Aᴰ Bᴰ .fst
          Quo*⇒ᴰ {A} {B} Aᴰ Bᴰ .snd .fst = ⇒ᴰ Aᴰ Bᴰ .snd .fst
          Quo*⇒ᴰ {A} {B} Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.inv a x = ⇒ᴰ.λᴰ Aᴰ Bᴰ x
          Quo*⇒ᴰ {A} {B} Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.rightInv b q = Quo*Cᴰ.rectifyOut
            {!!}
          Quo*⇒ᴰ {A} {B} Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.leftInv = {!!}
          -- Quo*⇒ᴰ Aᴰ Bᴰ = ?
          -- --   = ⇒ᴰ Aᴰ Bᴰ .fst
          -- -- Quo*⇒ᴰ Aᴰ Bᴰ .snd .fst = ⇒ᴰ Aᴰ Bᴰ .snd .fst
          -- -- Quo*⇒ᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.inv a = ⇒ᴰ.λᴰ Aᴰ Bᴰ
          -- -- Quo*⇒ᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.rightInv = {!!}
          -- -- Quo*⇒ᴰ Aᴰ Bᴰ .snd .snd Γ Γᴰ .isIsoOver.leftInv = {!!}
          -- module _ (ı-const : {A : Ty} (f : Constant A) → Quo*Cᴰ.Hom[ gen f ][ termᴰ .fst , elimOb Quo*Cᴰ Quo*termᴰ Quo*bpᴰ Quo*⇒ᴰ ı A ])-- need to get an interpretation of the constants here
          --   where

          --   unQuoElim : GlobalSection Quo*Cᴰ
          --   unQuoElim = elim Quo*Cᴰ Quo*termᴰ Quo*bpᴰ Quo*⇒ᴰ ı ı-const

          --   module _ (ı-ax : ∀ {A M N} → (eq : Axiom {A} M N) → unQuoElim .F-homᴰ M Cᴰ.≡[ eq/ M N (ax eq) ] unQuoElim .F-homᴰ N) where
          --     elimQuoHomᴰ : ∀ {Γ A} (M N : Tm Γ A) (M≈N : M ≈ N) → unQuoElim .F-homᴰ M Cᴰ.∫≡ unQuoElim .F-homᴰ N
          --     elimQuoHomᴰ M N (refl≈ γ) = refl
          --     elimQuoHomᴰ _ _ (⋆≈ M≈N M'≈N') = Cᴰ.⟨ elimQuoHomᴰ _ _ M≈N ⟩⋆⟨ elimQuoHomᴰ _ _ M'≈N' ⟩
          --     elimQuoHomᴰ M N ([λ]≈ M≈N) = ⇒ᴰ.cong-λᴰ _ _ (elimQuoHomᴰ _ _ M≈N)
          --     elimQuoHomᴰ M N (,x=≈ γ≈γ' M≈M') = bpᴰ.cong-introᴰ _ _ (ΣPathPᴰ (elimQuoHomᴰ _ _ γ≈γ') (elimQuoHomᴰ _ _ M≈M'))
          --     elimQuoHomᴰ M N (ax x) = Cᴰ.≡in (ı-ax x)

          --     elimQuo : GlobalSection Cᴰ
          --     elimQuo .F-obᴰ = elimCtx Quo*Cᴰ Quo*termᴰ Quo*bpᴰ Quo*⇒ᴰ ı
          --     elimQuo .F-homᴰ = Quo.elim (λ _ → Cᴰ.isSetHomᴰ) (unQuoElim .F-homᴰ) λ M N M≈N → Cᴰ.rectifyOut $ elimQuoHomᴰ M N M≈N
          --     elimQuo .F-idᴰ = refl
          --     elimQuo .F-seqᴰ = Quo.elimProp2 (λ γ≈ M≈ → Cᴰ.isSetHomᴰ _ _) $ λ γ M → refl

