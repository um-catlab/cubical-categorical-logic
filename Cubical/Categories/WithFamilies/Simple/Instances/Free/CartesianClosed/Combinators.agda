{-# OPTIONS -WnoUnsupportedIndexedMatch #-}
{-# OPTIONS --lossy-unification #-}

-- Free CCC SCwF, defined using combinator syntax/explicit substitutions
module Cubical.Categories.WithFamilies.Simple.Instances.Free.CartesianClosed.Combinators where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.More

open import Cubical.Data.FinData hiding (elim)
open import Cubical.Data.List hiding (elim)
open import Cubical.Data.List.FinData
open import Cubical.Data.List.Dependent
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Constructions.Fiber hiding (fiber)
open import Cubical.Categories.Constructions.TotalCategory using (∫C)
open import Cubical.Categories.Functor
open import Cubical.Categories.Limits.Terminal.More
open import Cubical.Categories.Presheaf
open import Cubical.Categories.Presheaf.Morphism.Alt
open import Cubical.Categories.Presheaf.Constructions
open import Cubical.Categories.Presheaf.More

open import Cubical.Categories.Displayed.Base
open import Cubical.Categories.Displayed.Functor
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf

open import Cubical.Categories.WithFamilies.Simple.Base
open import Cubical.Categories.WithFamilies.Simple.Displayed
open import Cubical.Categories.WithFamilies.Simple.Properties
open import Cubical.Categories.WithFamilies.Simple.TypeStructure.Functions

private
  variable
    ℓ ℓ' ℓC ℓC' ℓT ℓT' : Level

open Category
open Functor
open Functorᴰ
open Section
open UniversalElement
open PshIso
open PshHom

module _ (Σ₀ : Type ℓ) where
  data Ty : Type ℓ where
    gen : Σ₀ → Ty
    [𝟙] : Ty
    _[×]_ _[⇒]_ : Ty → Ty → Ty

  Ctx = List Ty

  record Operations (ℓ' : Level) : Type (ℓ-max ℓ $ ℓ-suc ℓ') where
    constructor operations
    field
      ops : Type ℓ'
      cod : ops → Ty
      dom : ops → Ctx

  module _ (Σ₁ : Operations ℓ') where
    open Operations Σ₁
    data Tm : (Γ : Ctx) → Ty → Type (ℓ-max ℓ ℓ')
    data Subst : (Γ : Ctx) → Ctx → Type (ℓ-max ℓ ℓ')
    var' : ∀ {Γ A} → Tm (A ∷ Γ) A
    sbst' : ∀ {Δ Γ A} → (γ : Subst Δ Γ) (M : Tm Γ A) → Tm Δ A

    data Subst where
      -- category structure
      idS  : ∀ {Γ} → Subst Γ Γ
      seqS : ∀ {Γ Δ Θ} (δ : Subst Γ Δ) (θ : Subst Δ Θ) → Subst Γ Θ
      seqAssoc : ∀ {Γ Δ Θ H} (γ : Subst H Γ)(δ : Subst Γ Δ)(θ : Subst Δ Θ)
        → seqS γ (seqS δ θ) ≡ seqS (seqS γ δ) θ
      seqIdL :  ∀ {Γ Δ} (δ : Subst Γ Δ)
        → seqS idS δ ≡ δ
      seqIdR :  ∀ {Γ Δ} (δ : Subst Γ Δ)
        → seqS δ idS ≡ δ
      isSetSubst : ∀ Γ Δ → isSet (Subst Γ Δ)

      -- terminal object
      [] : ∀ {Γ} → Subst Γ []
      []η : ∀ {Γ} (δ : Subst Γ []) → δ ≡ []

      -- comprehension object
      _∷_ : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Subst Γ Δ) → Subst Γ (A ∷ Δ)
      wk : ∀ {Γ A} → Subst (A ∷ Γ) Γ
      wkβ : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Subst Γ Δ)
        → seqS (M ∷ δ) wk ≡ δ
      ∷η : ∀ {Γ Δ A} (δ,M : Subst Γ (A ∷ Δ))
        → δ,M ≡ (sbst' δ,M var' ∷ seqS δ,M wk)
    data Tm where
      -- generators
      op : ∀ (o : ops) → Tm (dom o) (cod o)

      -- presheaf structure
      sbst : ∀ {Δ Γ A} → (γ : Subst Δ Γ) (M : Tm Γ A) → Tm Δ A
      sbstAssoc : ∀ {Θ Δ Γ A} (δ : Subst Θ Δ) (γ : Subst Δ Γ) (M : Tm Γ A)
        → sbst (seqS δ γ) M ≡ sbst δ (sbst γ M)
      sbstIdL : ∀ {Γ A} → (M : Tm Γ A)
        → sbst idS M ≡ M
      isSetTm : ∀ Γ A → isSet (Tm Γ A)

      -- comprehension π2
      var : ∀ {Γ A} → Tm (A ∷ Γ) A
      varβ : ∀ {Γ Δ A} (M : Tm Γ A) (δ : Subst Γ Δ)
        → sbst (M ∷ δ) var ≡ M

      -- function types
      [app] : ∀ {Γ A B} → Tm Γ (A [⇒] B) → Tm Γ A → Tm Γ B
      [λ]   : ∀ {Γ A B} → Tm (A ∷ Γ) B → Tm Γ (A [⇒] B)
      -- natural
      [app]-natural : ∀ {Δ Γ A B}
        (γ : Subst Δ Γ)(M : Tm Γ (A [⇒] B))(N : Tm Γ A)
        → sbst γ ([app] M N) ≡ [app] (sbst γ M) (sbst γ N)
      -- isomorphism
      [⇒]β : ∀ {Γ A B}
        → (M : Tm (A ∷ Γ) B)
        → [app] (sbst wk ([λ] M)) var ≡ M
      [⇒]η : ∀ {Γ A B}
        → (M : Tm Γ (A [⇒] B))
        → [λ] ([app] (sbst wk M) var) ≡ M

    var' = var
    sbst' = sbst

    -- The category of contexts and substitutions
    CTX : Category ℓ (ℓ-max ℓ ℓ')
    CTX .ob = Ctx
    CTX .Hom[_,_] Γ Δ = Subst Γ Δ
    CTX .id = idS
    CTX ._⋆_ = seqS
    CTX .⋆IdL = seqIdL
    CTX .⋆IdR = seqIdR
    CTX .⋆Assoc γ δ θ = sym (seqAssoc γ δ θ)
    CTX .isSetHom = isSetSubst _ _

    TM : Ty → Presheaf CTX (ℓ-max ℓ ℓ')
    TM A .F-ob Γ = Tm Γ A , isSetTm Γ A
    TM A .F-hom γ M = sbst γ M
    TM A .F-id = funExt sbstIdL
    TM A .F-seq γ δ = funExt (λ M → sbstAssoc δ γ M)

    term' : Terminal' CTX
    term' .vertex = []
    term' .element = tt
    term' .universal Γ .equiv-proof y = uniqueExists [] refl (λ _ → isSetUnit _ _) 
      λ δ _ → sym ([]η δ)

    EXT : (A : Ty) → LocallyRepresentable (TM A)
    EXT A Γ .vertex = A ∷ Γ
    EXT A Γ .element = wk , var
    EXT A Γ .universal Δ = isIsoToIsEquiv 
      ( (λ (γ , M) → M ∷ γ)
      , (λ (γ , M) → ΣPathP (wkβ M γ , varβ M γ))
      , λ δ → sym (∷η δ))

    FreeCwF : SCwF ℓ (ℓ-max ℓ ℓ') ℓ (ℓ-max ℓ ℓ')
    FreeCwF .fst = CTX
    FreeCwF .snd .fst = Ty
    FreeCwF .snd .snd .fst = TM
    FreeCwF .snd .snd .snd .fst = term'
    FreeCwF .snd .snd .snd .snd = EXT

    FreeFunTypes : FunTypes FreeCwF
    FreeFunTypes A B .fst = A [⇒] B
    FreeFunTypes A B .snd .trans .N-ob = λ Γ M → [app] (sbst wk M) var
    FreeFunTypes A B .snd .trans .N-hom Δ Γ γ M⟨x⟩ =
      sym $ [app]-natural _ _ _
      ∙ cong₂ [app]
        (sym (sbstAssoc _ _ _) ∙ cong₂ sbst (wkβ var (seqS wk γ)) refl ∙ sbstAssoc _ _ _)
        (varβ var (seqS wk γ))
    FreeFunTypes A B .snd .nIso Γ .fst = [λ]
    FreeFunTypes A B .snd .nIso Γ .snd .fst = [⇒]β
    FreeFunTypes A B .snd .nIso Γ .snd .snd = [⇒]η
