module Cubical.Algebra.Theory where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.More
open import Cubical.Data.Sigma

variable
  ℓ ℓᴰ ℓ' ℓᴰ' ℓ'' ℓᴰ'' ℓO ℓA ℓE : Level

record Signature ℓO ℓA : Type (ℓ-max (ℓ-suc ℓO) (ℓ-suc ℓA)) where
  field
    Op : Type ℓO
    Arity : Op → Type ℓA

  AlgebraWithCarrier : (X : Type ℓ) → Type (ℓ-max (ℓ-max ℓO ℓA) ℓ)
  AlgebraWithCarrier X = ∀ (f : Op) → (ρ : Arity f → X) → X

  Algebra : ∀ ℓ → Type _
  Algebra ℓ = Σ[ X ∈ Type ℓ ] AlgebraWithCarrier X

  module _ (A : Algebra ℓ) where
    -- Twist on the more obvious definition of displayed Algebra:
    -- essentially build in a substitution here.
    AlgebraᴰWithCarrier : (A .fst → Type ℓᴰ) → Type _
    AlgebraᴰWithCarrier Xᴰ =
      ∀ (f : Op) (ρ : Arity f → A .fst)
        (ρᴰ : (v : Arity f) → Xᴰ (ρ v))
        (f⟨ρ⟩ : A .fst) (f∘ρ≡f⟨ρ⟩ : A .snd f ρ ≡ f⟨ρ⟩)
      → Xᴰ f⟨ρ⟩

    -- this is the more obvious definition, which is basically "Yoneda Expanded"
    AlgebraᴰWithCarrier' : (A .fst → Type ℓᴰ) → Type _
    AlgebraᴰWithCarrier' Xᴰ =
      ∀ (f : Op) (ρ : Arity f → A .fst)
        (ρᴰ : (v : Arity f) → Xᴰ (ρ v))
      → Xᴰ (A .snd f ρ)

    AlgebraᴰWithCarrier'≃AlgebraᴰWithCarrier :
      (Xᴰ : A .fst → Type ℓᴰ)
      → AlgebraᴰWithCarrier' Xᴰ ≃ AlgebraᴰWithCarrier Xᴰ
    AlgebraᴰWithCarrier'≃AlgebraᴰWithCarrier Xᴰ =
      isoToEquiv (iso generalize specialize generalize-specialize specialize-generalize)
      where
      generalize : AlgebraᴰWithCarrier' Xᴰ → AlgebraᴰWithCarrier Xᴰ
      generalize α f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ =
        J (λ f⟨ρ⟩ _ → Xᴰ f⟨ρ⟩) (α f ρ ρᴰ) f∘ρ≡f⟨ρ⟩

      specialize : AlgebraᴰWithCarrier Xᴰ → AlgebraᴰWithCarrier' Xᴰ
      specialize α f ρ ρᴰ = α f ρ ρᴰ (A .snd f ρ) refl

      generalize-specialize : (d : AlgebraᴰWithCarrier Xᴰ)
        → generalize (specialize d) ≡ d
      generalize-specialize d =
        funExt λ f → funExt λ ρ → funExt λ ρᴰ →
          funExt λ f⟨ρ⟩ → funExt λ f∘ρ≡f⟨ρ⟩ →
            J (λ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ →
                generalize (specialize d) f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩
                  ≡ d f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩)
              (JRefl (λ f⟨ρ⟩ _ → Xᴰ f⟨ρ⟩)
                (d f ρ ρᴰ (A .snd f ρ) refl))
              f∘ρ≡f⟨ρ⟩

      specialize-generalize : (d : AlgebraᴰWithCarrier' Xᴰ)
        → specialize (generalize d) ≡ d
      specialize-generalize d =
        funExt λ f → funExt λ ρ → funExt λ ρᴰ →
          JRefl (λ f⟨ρ⟩ _ → Xᴰ f⟨ρ⟩) (d f ρ ρᴰ)

    Algebraᴰ : ∀ ℓᴰ → Type _
    Algebraᴰ ℓᴰ = Σ[ Xᴰ ∈ (A .fst → Type ℓᴰ) ] AlgebraᴰWithCarrier Xᴰ

  ∫Algebra : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ) → Algebra (ℓ-max ℓ ℓᴰ)
  ∫Algebra Aᴰ .fst = Σ[ a ∈ _ ] Aᴰ .fst a
  ∫Algebra {A = A} Aᴰ .snd f ρ .fst = A .snd f (λ z → ρ z .fst)
  ∫Algebra Aᴰ .snd f ρ .snd = Aᴰ .snd _ _ (λ v → ρ v .snd) _ refl

  record Section {A : Algebra ℓ}(Aᴰ : Algebraᴰ A ℓᴰ)
    : Type (ℓ-max ℓ (ℓ-max ℓᴰ (ℓ-max ℓA ℓO))) where
    eta-equality
    field
      fun : ∀ a → (Aᴰ .fst a)
      homo : ∀ (f : Op)(γ : Arity f → A .fst) f⟨γ⟩
        → (f∘γ≡f⟨γ⟩ : A .snd f γ ≡ f⟨γ⟩)
        → Aᴰ .snd f γ (λ v → fun (γ v)) f⟨γ⟩ f∘γ≡f⟨γ⟩
            ≡ fun f⟨γ⟩

  wkAlg : (A : Algebra ℓ) (B : Algebra ℓ') → Algebraᴰ A ℓ'
  wkAlg A B .fst _ = B .fst
  wkAlg A B .snd f _ ρ _ _ = B .snd f ρ

  Homo : (A : Algebra ℓ) (B : Algebra ℓ') → Type _
  Homo A B = Section (wkAlg A B)

  idHomo : {A : Algebra ℓ} → Homo A A
  idHomo .Section.fun = λ a → a
  idHomo .Section.homo f γ f⟨γ⟩ pf = pf

  module _ {A : Algebra ℓ}{B : Algebra ℓ'} where
    _*_ : Homo A B → Algebraᴰ B ℓᴰ → Algebraᴰ A ℓᴰ
    (ϕ * Bᴰ) .fst a = Bᴰ .fst (ϕ .Section.fun a)
    (ϕ * Bᴰ) .snd f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ =
      Bᴰ .snd f (λ z → ϕ .Section.fun (ρ z)) ρᴰ
        (ϕ .Section.fun f⟨ρ⟩)
        (ϕ .Section.homo f ρ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩)

    module _ {Bᴰ : Algebraᴰ B ℓᴰ} where
      _⋆HS_ : (ϕ : Homo A B) → Section Bᴰ → Section (ϕ * Bᴰ)
      (ϕ ⋆HS Ψ) .Section.fun = λ a → Ψ .Section.fun (ϕ .Section.fun a)
      (ϕ ⋆HS Ψ) .Section.homo f γ f⟨γ⟩ f∘γ≡f⟨γ⟩ =
        Ψ .Section.homo f (λ v → ϕ .Section.fun (γ v))
          (ϕ .Section.fun f⟨γ⟩)
          (ϕ .Section.homo f γ f⟨γ⟩ f∘γ≡f⟨γ⟩)

    module _ {C : Algebra ℓE} where
      _⋆H_ : Homo A B → Homo B C → Homo A C
      ϕ ⋆H Ψ = ϕ ⋆HS Ψ

  module _ {A : Algebra ℓ}{B : Algebra ℓ'} where
    ⋆HIdR : (ϕ : Homo A B) → ϕ ⋆H idHomo ≡ ϕ
    ⋆HIdR ϕ = refl
  module _ {A : Algebra ℓ}{Aᴰ : Algebraᴰ A ℓᴰ} where
    ⋆HSIdL : (Ψ : Section Aᴰ) → idHomo ⋆HS Ψ ≡ Ψ
    ⋆HSIdL Ψ = refl
  module _ {A : Algebra ℓ}{B : Algebra ℓ'}{C : Algebra ℓ''}{Cᴰ : Algebraᴰ C ℓᴰ''} where
    ⋆HHSAssoc : (ϕ : Homo A B)(ψ : Homo B C)(χ : Section Cᴰ)
      → (ϕ ⋆H ψ) ⋆HS χ ≡ ϕ ⋆HS (ψ ⋆HS χ)
    ⋆HHSAssoc ϕ ψ χ = refl

  -- Free Algebras
  data |FreeAlg| (V : Type ℓ) : Type (ℓ-max (ℓ-max ℓ ℓO) ℓA) where
    var : V → |FreeAlg| V
    op : ∀ (f : Op) → (γ : Arity f → |FreeAlg| V) → |FreeAlg| V

  TmAlg : (V : Type ℓ) → Algebra (ℓ-max (ℓ-max ℓO ℓA) ℓ)
  TmAlg V .fst = |FreeAlg| V
  TmAlg V .snd = op

  module _ {V : Type ℓ} (Bᴰ : Algebraᴰ (TmAlg V) ℓᴰ) (ı : ∀ (v : V) → Bᴰ .fst (var v)) where
    elimFreeAlgfun : ∀ (M : |FreeAlg| V) → Bᴰ .fst M
    elimFreeAlgfun (var x) = ı x
    elimFreeAlgfun (op f γ) =
      Bᴰ .snd f γ (λ x → elimFreeAlgfun (γ x)) (op f γ) refl

    elimFreeAlg : Section Bᴰ
    elimFreeAlg .Section.fun = elimFreeAlgfun
    elimFreeAlg .Section.homo f γ f⟨γ⟩ f∘γ≡f⟨γ⟩ =
      J (λ f⟨γ⟩ f∘γ≡f⟨γ⟩ →
          Bᴰ .snd f γ (λ v → elimFreeAlgfun (γ v))
              f⟨γ⟩ f∘γ≡f⟨γ⟩
            ≡ elimFreeAlgfun f⟨γ⟩)
        refl f∘γ≡f⟨γ⟩

record Theory ℓO ℓA ℓO' ℓA' :
  Type (ℓ-max (ℓ-max (ℓ-suc ℓO) (ℓ-suc ℓA))
              (ℓ-max (ℓ-suc ℓO') (ℓ-suc ℓA'))) where
  field
    S : Signature ℓO ℓA
  open Signature S public hiding (Section; _*_)
  field
    Eq : Type ℓO'
    EqArity : Eq → Type ℓA'
    lhs rhs : ∀ (e : Eq) → |FreeAlg| (EqArity e)

  interp : (A : Algebra ℓ) {V : Type ℓ'} → (V → A .fst) → |FreeAlg| V → A .fst
  interp A ρ (var v) = ρ v
  interp A ρ (op f γ) = A .snd f (λ v → interp A ρ (γ v))

  IsModel : Algebra ℓ → Type _
  IsModel A = ∀ e (ρ : EqArity e → A .fst)
    → interp A ρ (lhs e) ≡ interp A ρ (rhs e)

  Model : ∀ ℓ → Type _
  Model ℓ = Σ[ A ∈ Algebra ℓ ]
    Σ[ _ ∈ IsModel A ] isSet (A .fst)

  interpᴰ : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ)
    {V : Type ℓ'} (ρ : V → A .fst)
    (ρᴰ : (v : V) → Aᴰ .fst (ρ v)) (t : |FreeAlg| V)
    → Aᴰ .fst (interp A ρ t)
  interpᴰ Aᴰ ρ ρᴰ (var v) = ρᴰ v
  interpᴰ {A = A} Aᴰ ρ ρᴰ (op f γ) =
    Aᴰ .snd f
      (λ v → interp A ρ (γ v))
      (λ v → interpᴰ Aᴰ ρ ρᴰ (γ v))
      (A .snd f (λ v → interp A ρ (γ v))) refl

  Algebraᴰ-op-filler : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ)
    (f : Op) (rho : Arity f → A .fst)
    (rhoᴰ : (v : Arity f) → Aᴰ .fst (rho v))
    (f⟨rho⟩ : A .fst) (f∘rho≡f⟨rho⟩ : A .snd f rho ≡ f⟨rho⟩)
    → Path (∫Algebra Aᴰ .fst)
        ( A .snd f rho
        , Aᴰ .snd f rho rhoᴰ (A .snd f rho) refl)
        ( f⟨rho⟩
        , Aᴰ .snd f rho rhoᴰ f⟨rho⟩ f∘rho≡f⟨rho⟩)
  Algebraᴰ-op-filler {A = A} Aᴰ f rho rhoᴰ f⟨rho⟩ f∘rho≡f⟨rho⟩ =
    J (λ f⟨rho⟩ f∘rho≡f⟨rho⟩ →
        Path (∫Algebra Aᴰ .fst)
          ( A .snd f rho
          , Aᴰ .snd f rho rhoᴰ (A .snd f rho) refl)
          ( f⟨rho⟩
          , Aᴰ .snd f rho rhoᴰ f⟨rho⟩ f∘rho≡f⟨rho⟩))
      refl f∘rho≡f⟨rho⟩

  interpPullback : {A : Algebra ℓ} {B : Algebra ℓ'}
    (phi : Homo A B) (Bᴰ : Algebraᴰ B ℓᴰ)
    {V : Type ℓ''} (rho : V → A .fst)
    (rhoᴰ : (v : V) → Bᴰ .fst (phi .Signature.Section.fun (rho v)))
    (t : |FreeAlg| V)
    → Path (∫Algebra Bᴰ .fst)
        ( interp B (λ v → phi .Signature.Section.fun (rho v)) t
        , interpᴰ Bᴰ (λ v → phi .Signature.Section.fun (rho v)) rhoᴰ t)
        ( phi .Signature.Section.fun (interp A rho t)
        , interpᴰ (Signature._*_ S phi Bᴰ) rho rhoᴰ t)
  interpPullback phi Bᴰ rho rhoᴰ (var v) = refl
  interpPullback {A = A} phi Bᴰ rho rhoᴰ (op f gamma) =
    cong (∫Algebra Bᴰ .snd f)
      (funExt λ v → interpPullback phi Bᴰ rho rhoᴰ (gamma v))
    ∙ Algebraᴰ-op-filler Bᴰ f
        (λ v → phi .Signature.Section.fun (interp A rho (gamma v)))
        (λ v →
          interpᴰ (Signature._*_ S phi Bᴰ) rho rhoᴰ (gamma v))
        (phi .Signature.Section.fun (A .snd f (λ v → interp A rho (gamma v))))
        (phi .Signature.Section.homo f
          (λ v → interp A rho (gamma v))
          (A .snd f (λ v → interp A rho (gamma v))) refl)

  IsModelᴰ : (M : Model ℓ) → Algebraᴰ (M .fst) ℓᴰ → Type _
  IsModelᴰ M Aᴰ =
    ∀ e (ρ : EqArity e → M .fst .fst)
      (ρᴰ : (v : EqArity e) → Aᴰ .fst (ρ v))
    → PathP (λ i → Aᴰ .fst (M .snd .fst e ρ i))
        (interpᴰ Aᴰ ρ ρᴰ (lhs e))
        (interpᴰ Aᴰ ρ ρᴰ (rhs e))

  Modelᴰ : Model ℓ → ∀ ℓᴰ → Type _
  Modelᴰ M ℓᴰ = Σ[ Aᴰ ∈ Algebraᴰ (M .fst) ℓᴰ ]
    Σ[ _ ∈ IsModelᴰ M Aᴰ ] ((a : M .fst .fst) → isSet (Aᴰ .fst a))

  interp∫ : {A : Algebra ℓ} {Aᴰ : Algebraᴰ A ℓᴰ}
    {V : Type ℓ'} (ρ : V → ∫Algebra Aᴰ .fst) (t : |FreeAlg| V)
    → interp (∫Algebra Aᴰ) ρ t ≡
      ( interp A (λ v → ρ v .fst) t
      , interpᴰ Aᴰ (λ v → ρ v .fst) (λ v → ρ v .snd) t)
  interp∫ ρ (var v) = refl
  interp∫ {Aᴰ = Aᴰ} ρ (op f γ) =
    cong (∫Algebra Aᴰ .snd f) (funExt λ v → interp∫ ρ (γ v))

  ∫Model : {M : Model ℓ} → Modelᴰ M ℓᴰ → Model (ℓ-max ℓ ℓᴰ)
  ∫Model Mᴰ .fst = ∫Algebra (Mᴰ .fst)
  ∫Model {M = M} Mᴰ .snd .fst e ρ =
    interp∫ ρ (lhs e)
    ∙ ΣPathP
        ( M .snd .fst e (λ v → ρ v .fst)
        , Mᴰ .snd .fst e (λ v → ρ v .fst) (λ v → ρ v .snd))
    ∙ sym (interp∫ ρ (rhs e))
  ∫Model {M = M} Mᴰ .snd .snd =
    isSetΣ (M .snd .snd) (Mᴰ .snd .snd)

  interpᴰwk : (M : Model ℓ) (N : Model ℓ') {V : Type ℓ''}
    (ρ : V → M .fst .fst) (ρᴰ : V → N .fst .fst) (t : |FreeAlg| V)
    → interpᴰ (wkAlg (M .fst) (N .fst)) ρ ρᴰ t ≡ interp (N .fst) ρᴰ t
  interpᴰwk M N ρ ρᴰ (var v) = refl
  interpᴰwk M N ρ ρᴰ (op f γ) =
    cong (N .fst .snd f) (funExt λ v → interpᴰwk M N ρ ρᴰ (γ v))

  wkModel : (M : Model ℓ) (N : Model ℓ') → Modelᴰ M ℓ'
  wkModel M N .fst = wkAlg (M .fst) (N .fst)
  wkModel M N .snd .fst e ρ ρᴰ =
    interpᴰwk M N ρ ρᴰ (lhs e)
    ∙ N .snd .fst e ρᴰ
    ∙ sym (interpᴰwk M N ρ ρᴰ (rhs e))
  wkModel M N .snd .snd _ = N .snd .snd

  module _ {M : Model ℓ} {N : Model ℓ'} where
    _*_ : Homo (M .fst) (N .fst) → Modelᴰ N ℓᴰ → Modelᴰ M ℓᴰ
    (phi * Nᴰ) .fst = Signature._*_ S phi (Nᴰ .fst)
    (phi * Nᴰ) .snd .fst e rho rhoᴰ =
      hSetReasoning.rectifyOut
        (N .fst .fst , N .snd .snd) (Nᴰ .fst .fst)
        ( sym (interpPullback phi (Nᴰ .fst) rho rhoᴰ (lhs e))
          ∙ ΣPathP
              ( N .snd .fst e
                  (λ v → phi .Signature.Section.fun (rho v))
              , Nᴰ .snd .fst e
                  (λ v → phi .Signature.Section.fun (rho v)) rhoᴰ)
          ∙ interpPullback phi (Nᴰ .fst) rho rhoᴰ (rhs e))
    (phi * Nᴰ) .snd .snd a =
      Nᴰ .snd .snd (phi .Signature.Section.fun a)

  -- Free Models
  module _ (V : Type ℓ) where
    data |FreeModel| :
      Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓO) ℓA) (ℓ-max ℓO' ℓA')) where
      var : V → |FreeModel|
      op : ∀ (f : Op) → (γ : Arity f → |FreeModel|) → |FreeModel|
      freeAlg : ∀ e → |FreeAlg| (EqArity e) → (EqArity e → |FreeModel|) → |FreeModel|
      freeAlgEqn : ∀ e → (γ : EqArity e → |FreeModel|)
        → freeAlg e (lhs e) γ ≡ freeAlg e (rhs e) γ
      freeAlg-var : ∀ e v (γ : EqArity e → |FreeModel|) → γ v ≡ freeAlg e (var v) γ
      freeAlg-op  : ∀ e f ρ (γ : EqArity e → |FreeModel|)
        → op f (λ x → freeAlg e (ρ x) γ) ≡ freeAlg e (op f ρ) γ
      isSetFreeModel : isSet |FreeModel|

    interpFreeAlg : ∀ e (t : |FreeAlg| (EqArity e))
      (ρ : EqArity e → |FreeModel|)
      → interp (|FreeModel| , |FreeModel|.op) ρ t ≡ freeAlg e t ρ
    interpFreeAlg e (|FreeAlg|.var v) ρ = freeAlg-var e v ρ
    interpFreeAlg e (|FreeAlg|.op f γ) ρ =
      cong (|FreeModel|.op f) (funExt λ v → interpFreeAlg e (γ v) ρ)
      ∙ freeAlg-op e f γ ρ

    FreeModel :
      Model (ℓ-max (ℓ-max (ℓ-max ℓ ℓO) ℓA) (ℓ-max ℓO' ℓA'))
    FreeModel .fst .fst = |FreeModel|
    FreeModel .fst .snd = |FreeModel|.op
    FreeModel .snd .fst e ρ =
      interpFreeAlg e (lhs e) ρ
      ∙ freeAlgEqn e ρ
      ∙ sym (interpFreeAlg e (rhs e) ρ)
    FreeModel .snd .snd = isSetFreeModel

    module _ (Bᴰ : Modelᴰ FreeModel ℓᴰ)
      (ı : (v : V) → Bᴰ .fst .fst (|FreeModel|.var v)) where
      private
        module BᴰReasoning =
          hSetReasoning (|FreeModel| , isSetFreeModel) (Bᴰ .fst .fst)

      freeAlgᴰ : ∀ e (t : |FreeAlg| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → Bᴰ .fst .fst (ρ v))
        → Bᴰ .fst .fst (freeAlg e t ρ)
      freeAlgᴰ e t ρ ρᴰ =
        BᴰReasoning.reind (interpFreeAlg e t ρ)
          (interpᴰ (Bᴰ .fst) ρ ρᴰ t)

      freeAlgᴰ-filler : ∀ e (t : |FreeAlg| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → Bᴰ .fst .fst (ρ v))
        → Path (∫Algebra (Bᴰ .fst) .fst)
            ( interp (FreeModel .fst) ρ t
            , interpᴰ (Bᴰ .fst) ρ ρᴰ t)
            (freeAlg e t ρ , freeAlgᴰ e t ρ ρᴰ)
      freeAlgᴰ-filler e t ρ ρᴰ =
        BᴰReasoning.reind-filler (interpFreeAlg e t ρ)

      elimFreeModelfun : (x : |FreeModel|) → Bᴰ .fst .fst x
      elimFreeModelfun (|FreeModel|.var v) = ı v
      elimFreeModelfun (|FreeModel|.op f γ) =
        Bᴰ .fst .snd f γ (λ v → elimFreeModelfun (γ v))
          (|FreeModel|.op f γ) refl
      elimFreeModelfun (freeAlg e t ρ) =
        freeAlgᴰ e t ρ (λ v → elimFreeModelfun (ρ v))
      elimFreeModelfun (freeAlgEqn e ρ i) =
        BᴰReasoning.rectifyOut {e' = freeAlgEqn e ρ}
          ( sym (freeAlgᴰ-filler e (lhs e) ρ
              (λ v → elimFreeModelfun (ρ v)))
            ∙ BᴰReasoning.≡in
                (Bᴰ .snd .fst e ρ (λ v → elimFreeModelfun (ρ v)))
            ∙ freeAlgᴰ-filler e (rhs e) ρ
                (λ v → elimFreeModelfun (ρ v))) i
      elimFreeModelfun (freeAlg-var e v ρ i) =
        BᴰReasoning.rectifyOut {e' = freeAlg-var e v ρ}
          (freeAlgᴰ-filler e (|FreeAlg|.var v) ρ
            (λ x → elimFreeModelfun (ρ x))) i
      elimFreeModelfun (freeAlg-op e f σ ρ i) =
        BᴰReasoning.rectifyOut {e' = freeAlg-op e f σ ρ}
          ( sym
              (cong (∫Algebra (Bᴰ .fst) .snd f)
                (funExt λ v →
                  freeAlgᴰ-filler e (σ v) ρ
                    (λ x → elimFreeModelfun (ρ x))))
            ∙ freeAlgᴰ-filler e (|FreeAlg|.op f σ) ρ
                (λ x → elimFreeModelfun (ρ x))) i
      elimFreeModelfun (isSetFreeModel x y p q i j) =
        isSet→isSetDep (Bᴰ .snd .snd)
          (elimFreeModelfun x) (elimFreeModelfun y)
          (cong elimFreeModelfun p) (cong elimFreeModelfun q)
          (isSetFreeModel x y p q) i j

      elimFreeModel : Signature.Section S (Bᴰ .fst)
      elimFreeModel .Signature.Section.fun = elimFreeModelfun
      elimFreeModel .Signature.Section.homo f γ f⟨γ⟩ f∘γ≡f⟨γ⟩ =
        J (λ f⟨γ⟩ f∘γ≡f⟨γ⟩ →
            Bᴰ .fst .snd f γ (λ v → elimFreeModelfun (γ v))
                f⟨γ⟩ f∘γ≡f⟨γ⟩
              ≡ elimFreeModelfun f⟨γ⟩)
          refl f∘γ≡f⟨γ⟩
