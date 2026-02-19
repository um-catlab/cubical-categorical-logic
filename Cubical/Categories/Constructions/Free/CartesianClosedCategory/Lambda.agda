{-# OPTIONS --lossy-unification #-}
module Cubical.Categories.Constructions.Free.CartesianClosedCategory.Lambda where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function

import Cubical.Data.Equality as Eq
open import Cubical.Data.List hiding (elim)
open import Cubical.Data.Unit
open import Cubical.Data.Sigma hiding (_×_)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
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
open import Cubical.Categories.Displayed.Section
open import Cubical.Categories.Displayed.Presheaf.Uncurried.UniversalProperties
open import Cubical.Categories.Displayed.Presheaf.Uncurried.Constructions.ExponentialD

private
  variable
    ℓ ℓ' ℓCᴰ ℓCᴰ' : Level

open Category
open Functor
open Section
open UniversalElement

module _ (Base : Type ℓ) where
  data Ty : Type ℓ where
    ↑ : Base → Ty
    _[⇒]_ : Ty → Ty → Ty

  module _ (Constant : Ty → Type ℓ') where

    Ctx = List Ty

    data Subst : (Δ : Ctx) (Γ : Ctx) → Type (ℓ-max ℓ ℓ')
    data Tm : (Γ : Ctx) (A : Ty) → Type (ℓ-max ℓ ℓ')
    var' : ∀ {Γ A} → Tm (A ∷ Γ) A
    sbst' : ∀ {Δ Γ A} → (γ : Subst Δ Γ) (M : Tm Γ A) → Tm Δ A
    data Subst where
      idS  : ∀ {Γ} → Subst Γ Γ
      seqS : ∀ {Γ Δ Θ} (δ : Subst Γ Δ) (θ : Subst Δ Θ) → Subst Γ Θ
      seqAssoc : ∀ {Γ Δ Θ H} (γ : Subst H Γ)(δ : Subst Γ Δ)(θ : Subst Δ Θ)
        → seqS (seqS γ δ) θ ≡ seqS γ (seqS δ θ)
      seqIdL :  ∀ {Γ Δ} (δ : Subst Γ Δ)
        → seqS idS δ ≡ δ
      seqIdR :  ∀ {Γ Δ} (δ : Subst Γ Δ)
        → seqS δ idS ≡ δ
      isSetSubst : ∀ {Γ Δ} → isSet (Subst Γ Δ)

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
      constant : ∀ {A} → (f : Constant A) → Tm [] A

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
      [λ]-natural : ∀ {Δ Γ A B}
        (γ : Subst Δ Γ)(M : Tm (A ∷ Γ) B)
        → [λ] (sbst (var ∷ seqS wk γ) M) ≡ sbst γ ([λ] M)
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

    LAMBDA : Category ℓ (ℓ-max ℓ ℓ')
    LAMBDA .ob = Ctx
    LAMBDA .Hom[_,_] = Subst
    LAMBDA .id = idS
    LAMBDA ._⋆_ = seqS
    LAMBDA .⋆IdL = seqIdL
    LAMBDA .⋆IdR = seqIdR
    LAMBDA .⋆Assoc = seqAssoc
    LAMBDA .isSetHom = isSetSubst

    TM : ∀ A → Presheaf LAMBDA (ℓ-max ℓ ℓ')
    TM A .F-ob Γ .fst = Tm Γ A
    TM A .F-ob Γ .snd = isSetTm Γ A
    TM A .F-hom = sbst
    TM A .F-id = funExt sbstIdL
    TM A .F-seq δ γ = funExt (sbstAssoc γ δ)

    TERMINALCTX : Terminal' LAMBDA
    TERMINALCTX .vertex = []
    TERMINALCTX .element = tt
    TERMINALCTX .universal Γ = isIsoToIsEquiv
      ((λ z → []) , ((λ _ → refl) , (λ γ⊤ → sym ([]η _))))

    EXTENSION : ∀ Γ A → UniversalElement LAMBDA ((LAMBDA [-, Γ ]) ×Psh TM A)
    EXTENSION Γ A .vertex = A ∷ Γ
    EXTENSION Γ A .element = wk , var
    EXTENSION Γ A .universal Δ = isIsoToIsEquiv
      ( (λ (γ , M) → M ∷ γ)
      , (λ (γ , M) → ≡-× (wkβ M γ) (varβ M γ))
      , (λ γ,M → sym (∷η γ,M)))

    SINGLE : ∀ A → PshIso (LAMBDA [-, [ A ] ]) (TM A)
    SINGLE A = yoRecIso (EXTENSION [] A)
      ⋆PshIso ×PshIso (yoRecIso TERMINALCTX) idPshIso
      ⋆PshIso Unit× (TM A)

    EXTENSION-× : ∀ A → BinProductsWith LAMBDA [ A ]
    EXTENSION-× A Γ =
      EXTENSION Γ A
      ◁PshIso (×PshIso idPshIso (invPshIso $ SINGLE A)
      ⋆PshIso eqToPshIso _ Eq.refl Eq.refl)

    EXPONENTIAL' : ∀ A B → PshIso ((_ , (EXTENSION-× A)) ⇒PshSmall TM B) (TM (A [⇒] B))
    EXPONENTIAL' A B .PshIso.trans .PshHom.N-ob Γ = [λ]
    EXPONENTIAL' A B .PshIso.trans .PshHom.N-hom Δ Γ γ M =
      cong [λ] (cong₂ sbst (λ i → varβ var [] i ∷ seqS wk γ) refl) ∙ [λ]-natural γ M
    EXPONENTIAL' A B .PshIso.nIso Γ .fst M = [app] (sbst wk M) var
    EXPONENTIAL' A B .PshIso.nIso Γ .snd .fst M = [⇒]η M
    EXPONENTIAL' A B .PshIso.nIso Γ .snd .snd M = [⇒]β M

    EXPONENTIALS : ∀ A B → Exponential LAMBDA [ A ] [ B ] (EXTENSION-× A)
    EXPONENTIALS A B = RepresentationPshIso→UniversalElement _
      ( [ A [⇒] B ] ,
        (SINGLE (A [⇒] B)
        ⋆PshIso invPshIso (EXPONENTIAL' A B)
        ⋆PshIso reindPshIso _ (invPshIso (SINGLE B))))

    module _ (Cᴰ : Categoryᴰ LAMBDA ℓCᴰ ℓCᴰ')
      where
      private
        module Cᴰ = Categoryᴰ Cᴰ
      module _
        (termᴰ : Terminalᴰ Cᴰ TERMINALCTX)
        (bpᴰ : ∀ {A} (Aᴰ : Cᴰ.ob[ [ A ] ]) → BinProductsWithᴰ Cᴰ (EXTENSION-× A) Aᴰ)
        (⇒ᴰ : ∀ {A B} (Aᴰ : Cᴰ.ob[ [ A ] ])(Bᴰ : Cᴰ.ob[ [ B ] ])
          → Exponentialᴰ Cᴰ ([ A ] , EXTENSION-× A) (Aᴰ , bpᴰ Aᴰ) Bᴰ (EXPONENTIALS A B))
        (ı : (A : Base) → Cᴰ.ob[ [ (↑ A) ] ]) where
        elimCtx : ∀ Γ → Cᴰ.ob[ Γ ]
        elimOb : ∀ A → Cᴰ.ob[ [ A ] ]
        elimCtx [] = termᴰ .fst -- Need Terminalᴰ
        elimCtx (A ∷ Γ) = bpᴰ (elimOb A) (elimCtx Γ) .fst

        elimOb (↑ x) = ı x
        elimOb (A [⇒] B) = ⇒ᴰ (elimOb A) (elimOb B) .fst

        module _ (ıf : ∀ {A} (f : Constant A) → Cᴰ.Hom[ constant f ∷ [] ][ elimCtx [] , elimOb A ]) where

          elimSubst : ∀ {Δ Γ} (γ : Subst Δ Γ) → Cᴰ.Hom[ γ ][ elimCtx Δ , elimCtx Γ ]
          elimTm : ∀ {Γ A} (M : Tm Γ A)
            → Cᴰ.Hom[ M ∷ [] ][ elimCtx Γ , elimOb A ]

          elimSubst {Δ} {Γ} idS = Cᴰ.idᴰ
          elimSubst {Δ} {Γ} (seqS γ γ₁) = elimSubst γ Cᴰ.⋆ᴰ elimSubst γ₁
          elimSubst {Δ} {Γ} (seqAssoc γ γ₁ γ₂ i) = {!!}
          elimSubst {Δ} {Γ} (seqIdL γ i) = {!!}
          elimSubst {Δ} {Γ} (seqIdR γ i) = {!!}
          elimSubst {Δ} {Γ} (isSetSubst γ γ₁ x y i i₁) = {!!}
          elimSubst {Δ} {Γ} [] = {!!}
          elimSubst {Δ} {Γ} ([]η γ i) = {!!}
          elimSubst {Δ} {Γ} (M ∷ γ) = {!!}
          elimSubst {Δ} {Γ} wk = bpᴰ (elimOb _) (elimCtx Γ) .snd .fst .fst
          elimSubst {Δ} {Γ} (wkβ M γ i) = {!!}
          elimSubst {Δ} {Γ} (∷η γ i) = {!!}

          elimTm (constant f) = ıf f
          elimTm (sbst γ M) = {!!}
          elimTm (sbstAssoc δ γ M i) = {!!}
          elimTm (sbstIdL M i) = {!!}
          elimTm (isSetTm Γ A M M₁ x y i i₁) = {!!}
          elimTm var = bpᴰ (elimOb _) (elimCtx _) .snd .fst .snd
          elimTm (varβ M δ i) = {!!}
          elimTm ([app] M M₁) = {!!}
          elimTm ([λ] M) = {!!}
          elimTm ([λ]-natural γ M i) = {!!}
          elimTm ([app]-natural γ M M₁ i) = {!!}
          elimTm ([⇒]β M i) = {!!}
          elimTm ([⇒]η M i) = {!!}

          elim : GlobalSection Cᴰ
          elim .F-obᴰ = elimCtx
          elim .F-homᴰ = elimSubst
          elim .F-idᴰ = refl
          elim .F-seqᴰ f g = refl
