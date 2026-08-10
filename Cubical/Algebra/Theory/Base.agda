module Cubical.Algebra.Theory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Foundations.HLevels.More
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Signature.Base public

variable
  ℓ ℓᴰ ℓᴰᴰ ℓ' ℓᴰ' ℓᴰᴰ' ℓ'' ℓᴰ'' ℓO ℓA ℓE : Level

record Theory ℓO ℓA ℓO' ℓA' :
  Type (ℓ-max (ℓ-max (ℓ-suc ℓO) (ℓ-suc ℓA))
              (ℓ-max (ℓ-suc ℓO') (ℓ-suc ℓA'))) where
  field
    S : Signature ℓO ℓA
  module S = Signature S
  open Signature S public
    hiding (_*_; *Id; *∘)
  field
    Eq : Type ℓO'
    EqArity : Eq → Type ℓA'
    lhs rhs : ∀ (e : Eq) → |FreeAlgebra| (EqArity e)

  IsModel : Algebra ℓ → Type _
  IsModel A = ∀ e (γ : EqArity e → A .fst)
    → recFA A γ .fst (lhs e) ≡ recFA A γ .fst (rhs e)

  Model : ∀ ℓ → Type _
  Model ℓ = Σ[ A ∈ Algebra ℓ ]
    Σ[ _ ∈ IsModel A ] isSet (A .fst)

  ⊤Model : Model ℓ-zero
  ⊤Model .fst = Unit , ⊤Algebra
  ⊤Model .snd .fst e ρ = refl
  ⊤Model .snd .snd = isSetUnit

  ⊤*Model : Model ℓ
  ⊤*Model .fst = Unit* , ⊤*Algebra
  ⊤*Model .snd .fst e ρ = refl
  ⊤*Model .snd .snd = isSetUnit*

  interp : (A : Algebra ℓ) {V : Type ℓ'}
    → (V → A .fst) → |FreeAlgebra| V → A .fst
  interp A ρ = recFA A ρ .fst

  interpᴰ : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ)
    {V : Type ℓ'} (ρ : V → A .fst)
    (ρᴰ : (v : V) → Aᴰ .fst (ρ v)) (t : |FreeAlgebra| V)
    → Aᴰ .fst (interp A ρ t)
  interpᴰ {A = A} Aᴰ ρ ρᴰ =
    elimFA (recFA A ρ S.* Aᴰ) ρᴰ .fst

  Algebraᴰ-op-filler : {A : Algebra ℓ} (Aᴰ : Algebraᴰ A ℓᴰ)
    (f : Op) (ρ : Arity f → A .fst)
    (ρᴰ : (v : Arity f) → Aᴰ .fst (ρ v))
    (f⟨ρ⟩ : A .fst) (f∘ρ≡f⟨ρ⟩ : A .snd f ρ ≡ f⟨ρ⟩)
    → Path (∫Algebra Aᴰ .fst)
        ( A .snd f ρ
        , Aᴰ .snd f ρ ρᴰ (A .snd f ρ) refl)
        ( f⟨ρ⟩
        , Aᴰ .snd f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩)
  Algebraᴰ-op-filler {A = A} Aᴰ f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ =
    J (λ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ →
        Path (∫Algebra Aᴰ .fst)
          ( A .snd f ρ
          , Aᴰ .snd f ρ ρᴰ (A .snd f ρ) refl)
          ( f⟨ρ⟩
          , Aᴰ .snd f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩))
      refl f∘ρ≡f⟨ρ⟩

  interpPullback : {A : Algebra ℓ} {B : Algebra ℓ'}
    (ϕ : S.Homo A B) (Bᴰ : Algebraᴰ B ℓᴰ)
    {V : Type ℓ''} (ρ : V → A .fst)
    (ρᴰ : (v : V) → Bᴰ .fst (ϕ .fst (ρ v)))
    (t : |FreeAlgebra| V)
    → Path (∫Algebra Bᴰ .fst)
        ( interp B (λ v → ϕ .fst (ρ v)) t
        , interpᴰ Bᴰ (λ v → ϕ .fst (ρ v)) ρᴰ t)
        ( ϕ .fst (interp A ρ t)
        , interpᴰ (ϕ S.* Bᴰ) ρ ρᴰ t)
  interpPullback ϕ Bᴰ ρ ρᴰ (var v) = refl
  interpPullback {A = A} {B = B} ϕ Bᴰ ρ ρᴰ (app f γ) =
    sym
      (Algebraᴰ-op-filler Bᴰ f
        (λ v → interp B (λ x → ϕ .fst (ρ x)) (γ v))
        (λ v → interpᴰ Bᴰ (λ x → ϕ .fst (ρ x)) ρᴰ (γ v))
        (interp B (λ x → ϕ .fst (ρ x)) (app f γ))
        (recFA B (λ x → ϕ .fst (ρ x)) .snd f γ
          (app f γ) refl))
    ∙ cong (∫Algebra Bᴰ .snd f)
      (funExt λ v → interpPullback ϕ Bᴰ ρ ρᴰ (γ v))
    ∙ Algebraᴰ-op-filler Bᴰ f
        (λ v → ϕ .fst (interp A ρ (γ v)))
        (λ v →
          interpᴰ (ϕ S.* Bᴰ) ρ ρᴰ (γ v))
        (ϕ .fst (interp A ρ (app f γ)))
        (ϕ .snd f
          (λ v → interp A ρ (γ v))
          (interp A ρ (app f γ))
          (recFA A ρ .snd f γ (app f γ) refl))

  interpHomo : {A : Algebra ℓ} {B : Algebra ℓ'}
    (ϕ : S.Homo A B) {V : Type ℓ''}
    (ρ : V → A .fst) (t : |FreeAlgebra| V)
    → interp B (λ v → ϕ .fst (ρ v)) t ≡ ϕ .fst (interp A ρ t)
  interpHomo ϕ ρ (var v) = refl
  interpHomo {A = A} {B = B} ϕ ρ (app f γ) =
    sym
      (recFA B (λ v → ϕ .fst (ρ v)) .snd f γ
        (app f γ) refl)
    ∙ cong (B .snd f) (funExt λ v → interpHomo ϕ ρ (γ v))
    ∙ ϕ .snd f
        (λ v → interp A ρ (γ v))
        (interp A ρ (app f γ))
        (recFA A ρ .snd f γ (app f γ) refl)

  IsModelᴰ : (M : Model ℓ) → Algebraᴰ (M .fst) ℓᴰ → Type _
  IsModelᴰ M Aᴰ =
    ∀ e (ρ : EqArity e → M .fst .fst)
      (ρᴰ : (v : EqArity e) → Aᴰ .fst (ρ v))
    → PathP (λ i → Aᴰ .fst (M .snd .fst e ρ i))
        (interpᴰ Aᴰ ρ ρᴰ (lhs e))
        (interpᴰ Aᴰ ρ ρᴰ (rhs e))

  ModelᴰWithCarrier : (M : Model ℓ)
    → (M .fst .fst → Type ℓᴰ) → Type _
  ModelᴰWithCarrier M Xᴰ =
    Σ[ αᴰ ∈ AlgebraᴰWithCarrier (M .fst) Xᴰ ]
      IsModelᴰ M (Xᴰ , αᴰ)

  Modelᴰ : Model ℓ → ∀ ℓᴰ → Type _
  Modelᴰ M ℓᴰ = Σ[ Aᴰ ∈ Algebraᴰ (M .fst) ℓᴰ ]
    Σ[ _ ∈ IsModelᴰ M Aᴰ ]
      ((a : M .fst .fst) → isSet (Aᴰ .fst a))

  isPropModelᴰStructure : (M : Model ℓ) (Aᴰ : Algebraᴰ (M .fst) ℓᴰ)
    → isProp
        (Σ[ _ ∈ IsModelᴰ M Aᴰ ]
          ((a : M .fst .fst) → isSet (Aᴰ .fst a)))
  isPropModelᴰStructure M Aᴰ (p , pSet) (q , qSet) i .fst e ρ ρᴰ =
    isOfHLevelPathP' 1 (pSet _) _ _ (p e ρ ρᴰ) (q e ρ ρᴰ) i
  isPropModelᴰStructure M Aᴰ (p , pSet) (q , qSet) i .snd =
    isPropΠ (λ _ → isPropIsSet) pSet qSet i

  Modelᴰ≡ : {M : Model ℓ} {Mᴰ Nᴰ : Modelᴰ M ℓᴰ}
    → Mᴰ .fst ≡ Nᴰ .fst → Mᴰ ≡ Nᴰ
  Modelᴰ≡ {M = M} = Σ≡Prop (isPropModelᴰStructure M)

  interp∫ : {A : Algebra ℓ} {Aᴰ : Algebraᴰ A ℓᴰ}
    {V : Type ℓ'} (ρ : V → ∫Algebra Aᴰ .fst) (t : |FreeAlgebra| V)
    → interp (∫Algebra Aᴰ) ρ t ≡
      ( interp A (λ v → ρ v .fst) t
      , interpᴰ Aᴰ (λ v → ρ v .fst) (λ v → ρ v .snd) t)
  interp∫ ρ (var v) = refl
  interp∫ {A = A} {Aᴰ = Aᴰ} ρ (app f γ) =
    sym
      (recFA (∫Algebra Aᴰ) ρ .snd f γ (app f γ) refl)
    ∙ cong (∫Algebra Aᴰ .snd f)
        (funExt λ v → interp∫ {A = A} {Aᴰ = Aᴰ} ρ (γ v))
    ∙ Algebraᴰ-op-filler Aᴰ f
        (λ v → interp A (λ x → ρ x .fst) (γ v))
        (λ v →
          interpᴰ Aᴰ (λ x → ρ x .fst) (λ x → ρ x .snd) (γ v))
        (interp A (λ x → ρ x .fst) (app f γ))
        (recFA A (λ x → ρ x .fst) .snd f γ
          (app f γ) refl)

  ∫Model : {M : Model ℓ} → Modelᴰ M ℓᴰ → Model (ℓ-max ℓ ℓᴰ)
  ∫Model Mᴰ .fst = ∫Algebra (Mᴰ .fst)
  ∫Model {M = M} Mᴰ .snd .fst e ρ =
    interp∫ {A = M .fst} {Aᴰ = Mᴰ .fst} ρ (lhs e)
    ∙ ΣPathP
        ( M .snd .fst e (λ v → ρ v .fst)
        , Mᴰ .snd .fst e (λ v → ρ v .fst) (λ v → ρ v .snd))
    ∙ sym (interp∫ {A = M .fst} {Aᴰ = Mᴰ .fst} ρ (rhs e))
  ∫Model {M = M} Mᴰ .snd .snd =
    isSetΣ (M .snd .snd) (Mᴰ .snd .snd)

  module _ {M : Model ℓ} where
    Modelᴰᴰ : (Mᴰ : Modelᴰ M ℓᴰ) → ∀ ℓᴰᴰ → Type _
    Modelᴰᴰ Mᴰ ℓᴰᴰ = Modelᴰ (∫Model {M = M} Mᴰ) ℓᴰᴰ

    ∫ᴰModel-assoc : {Mᴰ : Modelᴰ M ℓᴰ}
      (Mᴰᴰ : Modelᴰᴰ Mᴰ ℓᴰᴰ)
      → ∫Algebra (Mᴰᴰ .fst) .fst
      → ∫Algebra
          (S.∫ᴰAlgebra {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst)) .fst
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .fst = z .fst .fst
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .snd .fst = z .fst .snd
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .snd .snd = z .snd

    ∫ᴰModel-assocHomo : {Mᴰ : Modelᴰ M ℓᴰ}
      (Mᴰᴰ : Modelᴰᴰ Mᴰ ℓᴰᴰ)
      → S.Homo
          (∫Algebra (Mᴰᴰ .fst))
          (∫Algebra
            (S.∫ᴰAlgebra {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst)))
    ∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ .fst =
      ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ
    ∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .fst =
      op∘γ≡op⟨γ⟩ i .fst .fst
    ∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .snd .fst =
      op∘γ≡op⟨γ⟩ i .fst .snd
    ∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ i .snd .snd =
      op∘γ≡op⟨γ⟩ i .snd

    ∫ᴰModel : {Mᴰ : Modelᴰ M ℓᴰ}
      → Modelᴰᴰ Mᴰ ℓᴰᴰ → Modelᴰ M (ℓ-max ℓᴰ ℓᴰᴰ)
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .fst =
      S.∫ᴰAlgebra {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst)
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .snd .fst e ρ ρᴰ =
      hSetReasoning.rectifyOut
        (M .fst .fst , M .snd .snd)
        (S.∫ᴰAlgebra {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst) .fst)
        ( sym
            (interp∫
              {A = M .fst}
              {Aᴰ = S.∫ᴰAlgebra
                {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst)}
              (λ v → ρ v , ρᴰ v) (lhs e))
        ∙ interpHomo
            (∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ)
            (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd)
            (lhs e)
        ∙ cong (∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ)
            (∫Model
              {M = ∫Model {M = M} Mᴰ} Mᴰᴰ .snd .fst e
              (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd))
        ∙ sym
            (interpHomo
              (∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ)
              (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd)
              (rhs e))
        ∙ interp∫
            {A = M .fst}
            {Aᴰ = S.∫ᴰAlgebra {A = M .fst} {Aᴰ = Mᴰ .fst} (Mᴰᴰ .fst)}
            (λ v → ρ v , ρᴰ v) (rhs e))
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .snd .snd a =
      isSetΣ (Mᴰ .snd .snd a) (λ aᴰ → Mᴰᴰ .snd .snd (a , aᴰ))

  interpᴰwk : (M : Model ℓ) (N : Model ℓ') {V : Type ℓ''}
    (ρ : V → M .fst .fst) (ρᴰ : V → N .fst .fst) (t : |FreeAlgebra| V)
    → interpᴰ (wkAlg (M .fst) (N .fst)) ρ ρᴰ t ≡ interp (N .fst) ρᴰ t
  interpᴰwk M N ρ ρᴰ (var v) = refl
  interpᴰwk M N ρ ρᴰ (app f γ) =
    cong (N .fst .snd f) (funExt λ v → interpᴰwk M N ρ ρᴰ (γ v))
    ∙ recFA (N .fst) ρᴰ .snd f γ (app f γ) refl

  wkModel : (M : Model ℓ) (N : Model ℓ') → Modelᴰ M ℓ'
  wkModel M N .fst = wkAlg (M .fst) (N .fst)
  wkModel M N .snd .fst e ρ ρᴰ =
    interpᴰwk M N ρ ρᴰ (lhs e)
    ∙ N .snd .fst e ρᴰ
    ∙ sym (interpᴰwk M N ρ ρᴰ (rhs e))
  wkModel M N .snd .snd _ = N .snd .snd

  _×Model_ : (M : Model ℓ) (N : Model ℓ') → Model _
  M ×Model N = ∫Model {M = M} (wkModel M N)

  module _ {M : Model ℓ} {N : Model ℓ'} where
    _*_ : S.Homo (M .fst) (N .fst) → Modelᴰ N ℓᴰ → Modelᴰ M ℓᴰ
    (ϕ * Nᴰ) .fst = ϕ S.* (Nᴰ .fst)
    (ϕ * Nᴰ) .snd .fst e ρ ρᴰ =
      hSetReasoning.rectifyOut
        (N .fst .fst , N .snd .snd) (Nᴰ .fst .fst)
        ( sym (interpPullback ϕ (Nᴰ .fst) ρ ρᴰ (lhs e))
        ∙ ΣPathP
            ( N .snd .fst e (λ v → ϕ .fst (ρ v))
            , Nᴰ .snd .fst e (λ v → ϕ .fst (ρ v)) ρᴰ)
        ∙ interpPullback ϕ (Nᴰ .fst) ρ ρᴰ (rhs e))
    (ϕ * Nᴰ) .snd .snd a = Nᴰ .snd .snd (ϕ .fst a)

  module _ {M : Model ℓ} {Mᴰ : Modelᴰ M ℓᴰ} where
    *Id : _*_ {M = M} {N = M} (S.idHomo {A = M .fst}) Mᴰ ≡ Mᴰ
    *Id = Modelᴰ≡ {M = M}
      (S.*Id {A = M .fst} {Aᴰ = Mᴰ .fst})

  module _ {M : Model ℓ} {N : Model ℓ'} {P : Model ℓ''}
    {Pᴰ : Modelᴰ P ℓᴰ''}
    (ϕ : S.Homo (M .fst) (N .fst))
    (ψ : S.Homo (N .fst) (P .fst)) where
    *∘ : _*_ {M = M} {N = P}
          (S._⋆H_ {A = M .fst} {B = N .fst} {C = P .fst} ϕ ψ) Pᴰ
        ≡ _*_ {M = M} {N = N} ϕ
            (_*_ {M = N} {N = P} ψ Pᴰ)
    *∘ = Modelᴰ≡ {M = M}
      (S.*∘
        {A = M .fst} {B = N .fst} {C = P .fst} {Cᴰ = Pᴰ .fst}
        ϕ ψ)

  module _ (M : Model ℓ) where
    PathModel : Modelᴰ (M ×Model M) ℓ
    PathModel .fst = S.PathAlg (M .fst)
    PathModel .snd .fst e ρ ρᴰ =
      isProp→PathP (λ _ → M .snd .snd _ _)
        (interpᴰ (S.PathAlg (M .fst)) ρ ρᴰ (lhs e))
        (interpᴰ (S.PathAlg (M .fst)) ρ ρᴰ (rhs e))
    PathModel .snd .snd (m , n) =
      isProp→isSet (M .snd .snd m n)

    PathModelReflection : {Γ : Model ℓ'}
      (ϕ ψ : S.Homo (Γ .fst) (M .fst))
      → S.Section
          (S._*_
            {A = Γ .fst} {B = (M ×Model M) .fst}
            (S.×intro
              {Γ = Γ .fst} {A = M .fst} {B = M .fst} ϕ ψ)
            (PathModel .fst))
      → ϕ .fst ≡ ψ .fst
    PathModelReflection {Γ = Γ} ϕ ψ ϕ≡ψ =
      S.PathAlgReflection (M .fst)
        {Γ = Γ .fst} ϕ ψ ϕ≡ψ

  -- Free Models
  module _ (X : Type ℓ) where
    data |FreeModel| :
      Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓO) ℓA) (ℓ-max ℓO' ℓA')) where
      var : X → |FreeModel|
      app : ∀ (op : Op) → (γ : Arity op → |FreeModel|) → |FreeModel|
      freeAlg : ∀ e → |FreeAlgebra| (EqArity e) → (EqArity e → |FreeModel|) → |FreeModel|
      freeAlgEqn : ∀ e (γ : EqArity e → |FreeModel|)
        → freeAlg e (lhs e) γ ≡ freeAlg e (rhs e) γ
      freeAlg-var : ∀ e v (γ : EqArity e → |FreeModel|) → γ v ≡ freeAlg e (var v) γ
      freeAlg-op : ∀ e op γ (γ' : EqArity e → |FreeModel|)
        → app op (λ v → freeAlg e (γ v) γ') ≡ freeAlg e (app op γ) γ'
      isSetFreeModel : isSet |FreeModel|

    FreeModelAlgebra : Algebra _
    FreeModelAlgebra = |FreeModel| , app

    freeAlg≡recFA : ∀ e (t : |FreeAlgebra| (EqArity e))
      (γ : EqArity e → |FreeModel|)
      → recFA (|FreeModel| , app) γ .fst t ≡ freeAlg e t γ
    freeAlg≡recFA e (var x) γ = freeAlg-var e x γ
    freeAlg≡recFA e (app op γ) γ' =
      (λ i → app op (λ v → freeAlg≡recFA e (γ v) γ' i))
      ∙ freeAlg-op e op γ γ'

    FreeModel :
      Model (ℓ-max (ℓ-max (ℓ-max ℓ ℓO) ℓA) (ℓ-max ℓO' ℓA'))
    FreeModel .fst = FreeModelAlgebra
    FreeModel .snd .fst e γ =
      freeAlg≡recFA e (lhs e) γ
      ∙ freeAlgEqn e γ
      ∙ (sym $ freeAlg≡recFA e (rhs e) γ)
    FreeModel .snd .snd = isSetFreeModel

    module _ (Bᴰ : Modelᴰ FreeModel ℓᴰ) where
      private
        module BᴰReasoning =
          hSetReasoning (|FreeModel| , isSetFreeModel) (Bᴰ .fst .fst)

      freeAlgᴰ : ∀ e (t : |FreeAlgebra| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → Bᴰ .fst .fst (ρ v))
        → Bᴰ .fst .fst (freeAlg e t ρ)
      freeAlgᴰ e t ρ ρᴰ =
        BᴰReasoning.reind (freeAlg≡recFA e t ρ)
          (interpᴰ (Bᴰ .fst) ρ ρᴰ t)

      freeAlgᴰ-filler : ∀ e (t : |FreeAlgebra| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → Bᴰ .fst .fst (ρ v))
        → Path (∫Algebra (Bᴰ .fst) .fst)
            ( interp (FreeModel .fst) ρ t
            , interpᴰ (Bᴰ .fst) ρ ρᴰ t)
            (freeAlg e t ρ , freeAlgᴰ e t ρ ρᴰ)
      freeAlgᴰ-filler e t ρ ρᴰ =
        BᴰReasoning.reind-filler (freeAlg≡recFA e t ρ)

      module _ (ı : (x : X) → Bᴰ .fst .fst (|FreeModel|.var x)) where
        elimFreeModelfun : (t : |FreeModel|) → Bᴰ .fst .fst t
        elimFreeModelfun (var x) = ı x
        elimFreeModelfun (app op γ) =
          Bᴰ .fst .snd op γ (λ v → elimFreeModelfun (γ v))
            (app op γ) refl
        elimFreeModelfun (freeAlg e t ρ) =
          freeAlgᴰ e t ρ (λ v → elimFreeModelfun (ρ v))
        elimFreeModelfun (freeAlgEqn e ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlgEqn e ρ}
            ( sym
                (freeAlgᴰ-filler e (lhs e) ρ
                  (λ v → elimFreeModelfun (ρ v)))
            ∙ BᴰReasoning.≡in
                (Bᴰ .snd .fst e ρ (λ v → elimFreeModelfun (ρ v)))
            ∙ freeAlgᴰ-filler e (rhs e) ρ
                (λ v → elimFreeModelfun (ρ v))) i
        elimFreeModelfun (freeAlg-var e v ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlg-var e v ρ}
            (freeAlgᴰ-filler e (var v) ρ
              (λ x → elimFreeModelfun (ρ x))) i
        elimFreeModelfun (freeAlg-op e op γ ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlg-op e op γ ρ}
            ( sym
                (cong (∫Algebra (Bᴰ .fst) .snd op)
                  (funExt λ v →
                    freeAlgᴰ-filler e (γ v) ρ
                      (λ x → elimFreeModelfun (ρ x))))
            ∙ Algebraᴰ-op-filler (Bᴰ .fst) op
                (λ v → interp (FreeModel .fst) ρ (γ v))
                (λ v →
                  interpᴰ (Bᴰ .fst) ρ
                    (λ x → elimFreeModelfun (ρ x)) (γ v))
                (interp (FreeModel .fst) ρ (app op γ))
                (recFA (FreeModel .fst) ρ .snd op γ (app op γ) refl)
            ∙ freeAlgᴰ-filler e (app op γ) ρ
                (λ x → elimFreeModelfun (ρ x))) i
        elimFreeModelfun (isSetFreeModel x y p q i j) =
          isSet→isSetDep (Bᴰ .snd .snd)
            (elimFreeModelfun x) (elimFreeModelfun y)
            (cong elimFreeModelfun p) (cong elimFreeModelfun q)
            (isSetFreeModel x y p q) i j

        elimFreeModel : S.Section (Bᴰ .fst)
        elimFreeModel .fst = elimFreeModelfun
        elimFreeModel .snd f γ f⟨γ⟩ f∘γ≡f⟨γ⟩ =
          J (λ f⟨γ⟩ f∘γ≡f⟨γ⟩ →
              Bᴰ .fst .snd f γ (λ v → elimFreeModelfun (γ v))
                  f⟨γ⟩ f∘γ≡f⟨γ⟩
                ≡ elimFreeModelfun f⟨γ⟩)
            refl f∘γ≡f⟨γ⟩

    module _ (B : Model ℓ') where
      recFM : (X → B .fst .fst) → S.Homo (FreeModel .fst) (B .fst)
      recFM ı = elimFreeModel (wkModel FreeModel B) ı

      recFM-uniq : (f : S.Homo (FreeModel .fst) (B .fst))
        → f .fst ≡ recFM (f .fst ∘ var) .fst
      recFM-uniq f =
        PathModelReflection B {Γ = FreeModel} f g
          (elimFreeModel
            (_*_ {M = FreeModel} {N = B ×Model B}
              (S.×intro
                {Γ = FreeModel .fst} {A = B .fst} {B = B .fst} f g)
              (PathModel B))
            (λ _ → refl))
        where
        g : S.Homo (FreeModel .fst) (B .fst)
        g = recFM (f .fst ∘ var)

    module _ (Xᴰ : X → Type ℓᴰ) where
      data |FreeModelᴰ| : |FreeModel| →
        Type
          (ℓ-max (ℓ-max (ℓ-max ℓ ℓO) ℓA)
            (ℓ-max ℓᴰ (ℓ-max ℓO' ℓA'))) where
        var : ∀ {x} (xᴰ : Xᴰ x) → |FreeModelᴰ| (|FreeModel|.var x)
        app : ∀ op γ
          (γᴰ : (v : Arity op) → |FreeModelᴰ| (γ v))
          op⟨γ⟩
          (op∘γ≡op⟨γ⟩ : FreeModel .fst .snd op γ ≡ op⟨γ⟩)
          → |FreeModelᴰ| op⟨γ⟩
        freeAlg : ∀ e t ρ
          (ρᴰ : (v : EqArity e) → |FreeModelᴰ| (ρ v))
          → |FreeModelᴰ| (|FreeModel|.freeAlg e t ρ)
        freeAlgEqn : ∀ e ρ
          (ρᴰ : (v : EqArity e) → |FreeModelᴰ| (ρ v))
          → PathP (λ i →
              |FreeModelᴰ| (|FreeModel|.freeAlgEqn e ρ i))
              (freeAlg e (lhs e) ρ ρᴰ)
              (freeAlg e (rhs e) ρ ρᴰ)
        freeAlg-var : ∀ e v ρ
          (ρᴰ : (x : EqArity e) → |FreeModelᴰ| (ρ x))
          → PathP (λ i →
              |FreeModelᴰ| (|FreeModel|.freeAlg-var e v ρ i))
              (ρᴰ v)
              (freeAlg e (S.var v) ρ ρᴰ)
        freeAlg-op : ∀ e op γ ρ
          (ρᴰ : (x : EqArity e) → |FreeModelᴰ| (ρ x))
          → PathP (λ i →
              |FreeModelᴰ| (|FreeModel|.freeAlg-op e op γ ρ i))
              (app op
                (λ v → |FreeModel|.freeAlg e (γ v) ρ)
                (λ v → freeAlg e (γ v) ρ ρᴰ)
                (|FreeModel|.app op
                  (λ v → |FreeModel|.freeAlg e (γ v) ρ))
                refl)
              (freeAlg e (S.app op γ) ρ ρᴰ)
        isSetFreeModel : isSetᴰ |FreeModel|.isSetFreeModel |FreeModelᴰ|

      isSetFreeModelᴰ : (t : |FreeModel|) → isSet (|FreeModelᴰ| t)
      isSetFreeModelᴰ =
        isOfHLevelᴰ→isOfHLevel 2
          |FreeModel|.isSetFreeModel |FreeModelᴰ|.isSetFreeModel

      FreeModelAlgebraᴰ : Algebraᴰ (FreeModel .fst) _
      FreeModelAlgebraᴰ .fst = |FreeModelᴰ|
      FreeModelAlgebraᴰ .snd = |FreeModelᴰ|.app

      private
        module FreeModelᴰReasoning =
          hSetReasoning (|FreeModel| , |FreeModel|.isSetFreeModel)
            |FreeModelᴰ|

      freeAlgᴰ≡interpᴰ : ∀ e (t : |FreeAlgebra| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → |FreeModelᴰ| (ρ v))
        → Path (∫Algebra FreeModelAlgebraᴰ .fst)
            ( interp (FreeModel .fst) ρ t
            , interpᴰ FreeModelAlgebraᴰ ρ ρᴰ t)
            ( |FreeModel|.freeAlg e t ρ
            , |FreeModelᴰ|.freeAlg e t ρ ρᴰ)
      freeAlgᴰ≡interpᴰ e (S.var v) ρ ρᴰ i =
        |FreeModel|.freeAlg-var e v ρ i
        , |FreeModelᴰ|.freeAlg-var e v ρ ρᴰ i
      freeAlgᴰ≡interpᴰ e (S.app op γ) ρ ρᴰ =
        sym
          (Algebraᴰ-op-filler FreeModelAlgebraᴰ op
            (λ v → interp (FreeModel .fst) ρ (γ v))
            (λ v → interpᴰ FreeModelAlgebraᴰ ρ ρᴰ (γ v))
            (interp (FreeModel .fst) ρ (S.app op γ))
            (recFA (FreeModel .fst) ρ .snd op γ (S.app op γ) refl))
        ∙ cong (∫Algebra FreeModelAlgebraᴰ .snd op)
          (funExt λ v → freeAlgᴰ≡interpᴰ e (γ v) ρ ρᴰ)
        ∙ (λ i →
          |FreeModel|.freeAlg-op e op γ ρ i
          , |FreeModelᴰ|.freeAlg-op e op γ ρ ρᴰ i)

      FreeModelᴰ : Modelᴰ FreeModel _
      FreeModelᴰ .fst = FreeModelAlgebraᴰ
      FreeModelᴰ .snd .fst e ρ ρᴰ =
        FreeModelᴰReasoning.rectifyOut
          {e' = FreeModel .snd .fst e ρ}
          ( freeAlgᴰ≡interpᴰ e (lhs e) ρ ρᴰ
          ∙ (λ i →
              |FreeModel|.freeAlgEqn e ρ i
              , |FreeModelᴰ|.freeAlgEqn e ρ ρᴰ i)
          ∙ sym (freeAlgᴰ≡interpᴰ e (rhs e) ρ ρᴰ))
      FreeModelᴰ .snd .snd = isSetFreeModelᴰ

      module _ {A : Model ℓ'}
        (ϕ : S.Homo (FreeModel .fst) (A .fst))
        (Aᴰ : Modelᴰ A ℓᴰ')
        (ıᴰ : ∀ x → Xᴰ x → Aᴰ .fst .fst (ϕ .fst (|FreeModel|.var x)))
        where
        private
          Aᴰ' : Modelᴰ FreeModel ℓᴰ'
          Aᴰ' = _*_ {M = FreeModel} {N = A} ϕ Aᴰ

          module Aᴰ'Reasoning =
            hSetReasoning (|FreeModel| , |FreeModel|.isSetFreeModel)
              (Aᴰ' .fst .fst)

        |recFMᴰ| : ∀ {t} → |FreeModelᴰ| t → Aᴰ' .fst .fst t
        |recFMᴰ| (|FreeModelᴰ|.var {x = x} xᴰ) = ıᴰ x xᴰ
        |recFMᴰ| (|FreeModelᴰ|.app
          op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
          Aᴰ' .fst .snd op γ (λ v → |recFMᴰ| (γᴰ v))
            op⟨γ⟩ op∘γ≡op⟨γ⟩
        |recFMᴰ| (|FreeModelᴰ|.freeAlg e t ρ ρᴰ) =
          freeAlgᴰ Aᴰ' e t ρ (λ v → |recFMᴰ| (ρᴰ v))
        |recFMᴰ| (|FreeModelᴰ|.freeAlgEqn e ρ ρᴰ i) =
          Aᴰ'Reasoning.rectifyOut
            {e' = |FreeModel|.freeAlgEqn e ρ}
            ( sym
                (freeAlgᴰ-filler Aᴰ' e (lhs e) ρ
                  (λ v → |recFMᴰ| (ρᴰ v)))
            ∙ Aᴰ'Reasoning.≡in
                (Aᴰ' .snd .fst e ρ (λ v → |recFMᴰ| (ρᴰ v)))
            ∙ freeAlgᴰ-filler Aᴰ' e (rhs e) ρ
                (λ v → |recFMᴰ| (ρᴰ v))) i
        |recFMᴰ| (|FreeModelᴰ|.freeAlg-var e v ρ ρᴰ i) =
          Aᴰ'Reasoning.rectifyOut
            {e' = |FreeModel|.freeAlg-var e v ρ}
            (freeAlgᴰ-filler Aᴰ' e (S.var v) ρ
              (λ x → |recFMᴰ| (ρᴰ x))) i
        |recFMᴰ| (|FreeModelᴰ|.freeAlg-op e op γ ρ ρᴰ i) =
          Aᴰ'Reasoning.rectifyOut
            {e' = |FreeModel|.freeAlg-op e op γ ρ}
            ( sym
                (cong (∫Algebra (Aᴰ' .fst) .snd op)
                  (funExt λ v →
                    freeAlgᴰ-filler Aᴰ' e (γ v) ρ
                      (λ x → |recFMᴰ| (ρᴰ x))))
            ∙ Algebraᴰ-op-filler (Aᴰ' .fst) op
                (λ v → interp (FreeModel .fst) ρ (γ v))
                (λ v →
                  interpᴰ (Aᴰ' .fst) ρ
                    (λ x → |recFMᴰ| (ρᴰ x)) (γ v))
                (interp (FreeModel .fst) ρ (S.app op γ))
                (recFA (FreeModel .fst) ρ .snd op γ
                  (S.app op γ) refl)
            ∙ freeAlgᴰ-filler Aᴰ' e (S.app op γ) ρ
                (λ x → |recFMᴰ| (ρᴰ x))) i
        |recFMᴰ| (|FreeModelᴰ|.isSetFreeModel
          xᴰ yᴰ pᴰ qᴰ i j) =
          isSet→isSetDep (Aᴰ' .snd .snd)
            (|recFMᴰ| xᴰ) (|recFMᴰ| yᴰ)
            (λ k → |recFMᴰ| (pᴰ k)) (λ k → |recFMᴰ| (qᴰ k))
            (|FreeModel|.isSetFreeModel _ _ _ _) i j

        recFMᴰ : S.Homoᴰ ϕ (FreeModelᴰ .fst) (Aᴰ .fst)
        recFMᴰ .fst _ = |recFMᴰ|
        recFMᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
          op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
          J
            (λ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ →
              Aᴰ .fst .snd op (ϕ .fst ∘ γ)
                  (λ v → |recFMᴰ| (γᴰ v))
                  (ϕ .fst op⟨γ⟩)
                  (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
                ≡ |recFMᴰ| op⟨γᴰ⟩)
            refl
            op∘γᴰ≡op⟨γᴰ⟩

      module _ {A : Model ℓ'}
        (ϕ : S.Homo (FreeModel .fst) (A .fst))
        (Aᴰ : Modelᴰ A ℓᴰ')
        (ϕᴰ : S.Homoᴰ ϕ (FreeModelᴰ .fst) (Aᴰ .fst))
        where
        private
          ıᴰ : ∀ x → Xᴰ x → Aᴰ .fst .fst (ϕ .fst (|FreeModel|.var x))
          ıᴰ x xᴰ = ϕᴰ .fst _ (|FreeModelᴰ|.var xᴰ)

          baseϕ : S.Homo
            (∫Algebra (FreeModelᴰ .fst))
            (A .fst)
          baseϕ =
            S._⋆H_
              {A = ∫Algebra (FreeModelᴰ .fst)}
              {B = FreeModel .fst} {C = A .fst}
              (S.Fst {Aᴰ = FreeModelᴰ .fst}) ϕ

          ϕᴰSection : S.Section (baseϕ S.* (Aᴰ .fst))
          ϕᴰSection .fst z = ϕᴰ .fst (z .fst) (z .snd)
          ϕᴰSection .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
            ϕᴰ .snd op (fst ∘ γ) (snd ∘ γ)
              (op⟨γ⟩ .fst) (cong fst op∘γ≡op⟨γ⟩)
              (op⟨γ⟩ .snd)
              (S.Snd {Aᴰ = FreeModelᴰ .fst} .snd
                op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)

          ϕ∫ᴰ : S.Homo
            (∫Algebra (FreeModelᴰ .fst))
            (∫Algebra (Aᴰ .fst))
          ϕ∫ᴰ =
            S.∫intro
              {Γ = ∫Algebra (FreeModelᴰ .fst)}
              {A = A .fst} {B = Aᴰ .fst}
              baseϕ ϕᴰSection

          interpHomoFMᴰ : {V : Type ℓ''}
            (ρ : V → |FreeModel|)
            (ρᴰ : (v : V) → |FreeModelᴰ| (ρ v))
            (t : |FreeAlgebra| V)
            → Path (∫Algebra (Aᴰ .fst) .fst)
                ( interp (A .fst) (ϕ .fst ∘ ρ) t
                , interpᴰ (Aᴰ .fst) (ϕ .fst ∘ ρ)
                    (λ v → ϕᴰ .fst (ρ v) (ρᴰ v)) t)
                ( ϕ .fst (interp (FreeModel .fst) ρ t)
                , ϕᴰ .fst (interp (FreeModel .fst) ρ t)
                    (interpᴰ (FreeModelᴰ .fst) ρ ρᴰ t))
          interpHomoFMᴰ ρ ρᴰ t =
            sym
              (interp∫
                {A = A .fst} {Aᴰ = Aᴰ .fst}
                (λ v → ϕ .fst (ρ v) , ϕᴰ .fst (ρ v) (ρᴰ v)) t)
            ∙ interpHomo ϕ∫ᴰ (λ v → ρ v , ρᴰ v) t
            ∙ cong (ϕ∫ᴰ .fst)
                (interp∫
                  {A = FreeModel .fst} {Aᴰ = FreeModelᴰ .fst}
                  (λ v → ρ v , ρᴰ v) t)

          Aᴰ' : Modelᴰ FreeModel ℓᴰ'
          Aᴰ' = _*_ {M = FreeModel} {N = A} ϕ Aᴰ

          module AᴰReasoning =
            hSetReasoning (A .fst .fst , A .snd .snd) (Aᴰ .fst .fst)

          recᴰ : ∀ {t} → |FreeModelᴰ| t → Aᴰ .fst .fst (ϕ .fst t)
          recᴰ tᴰ = |recFMᴰ| {A = A} ϕ Aᴰ ıᴰ tᴰ

          pullbackTotal : ∫Algebra (Aᴰ' .fst) .fst
            → ∫Algebra (Aᴰ .fst) .fst
          pullbackTotal z .fst = ϕ .fst (z .fst)
          pullbackTotal z .snd = z .snd

          ηType : ∫Algebra (FreeModelᴰ .fst) .fst → Type _
          ηType z = ϕᴰ .fst (z .fst) (z .snd) ≡ recᴰ (z .snd)

          ηIsProp : (z : ∫Algebra (FreeModelᴰ .fst) .fst)
            → isProp (ηType z)
          ηIsProp z =
            Aᴰ .snd .snd (ϕ .fst (z .fst))
              (ϕᴰ .fst (z .fst) (z .snd)) (recᴰ (z .snd))

          app-η : ∀ op γ
            (γᴰ : (v : Arity op) → |FreeModelᴰ| (γ v))
            op⟨γ⟩ (op∘γ≡op⟨γ⟩ : FreeModel .fst .snd op γ ≡ op⟨γ⟩)
            → ((v : Arity op) →
                ϕᴰ .fst (γ v) (γᴰ v) ≡ recᴰ (γᴰ v))
            → ϕᴰ .fst op⟨γ⟩
                (|FreeModelᴰ|.app
                  op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
              ≡ recᴰ
                (|FreeModelᴰ|.app
                  op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
          app-η op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ γᴰ-η =
            sym
              (ϕᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
                (|FreeModelᴰ|.app
                  op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩)
                refl)
            ∙ cong
                (λ γᴰ' →
                  Aᴰ .fst .snd op (ϕ .fst ∘ γ) γᴰ'
                    (ϕ .fst op⟨γ⟩)
                    (ϕ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))
                (funExt γᴰ-η)

          freeAlg-η : ∀ e t ρ
            (ρᴰ : (v : EqArity e) → |FreeModelᴰ| (ρ v))
            → ((v : EqArity e) →
                ϕᴰ .fst (ρ v) (ρᴰ v) ≡ recᴰ (ρᴰ v))
            → ϕᴰ .fst (|FreeModel|.freeAlg e t ρ)
                (|FreeModelᴰ|.freeAlg e t ρ ρᴰ)
              ≡ recᴰ (|FreeModelᴰ|.freeAlg e t ρ ρᴰ)
          freeAlg-η e t ρ ρᴰ ρᴰ-η =
            AᴰReasoning.rectifyOut {e' = refl}
              ( sym
                  (cong (ϕ∫ᴰ .fst)
                    (freeAlgᴰ≡interpᴰ e t ρ ρᴰ))
              ∙ sym (interpHomoFMᴰ ρ ρᴰ t)
              ∙ cong
                  (λ ρᴰ' →
                    interp (A .fst) (ϕ .fst ∘ ρ) t
                    , interpᴰ (Aᴰ .fst) (ϕ .fst ∘ ρ) ρᴰ' t)
                  (funExt ρᴰ-η)
              ∙ interpPullback ϕ (Aᴰ .fst) ρ (λ v → recᴰ (ρᴰ v)) t
              ∙ cong pullbackTotal
                  (freeAlgᴰ-filler Aᴰ' e t ρ
                    (λ v → recᴰ (ρᴰ v))))

          |recFMᴰ|-η : ∀ {t} (tᴰ : |FreeModelᴰ| t)
            → ϕᴰ .fst t tᴰ ≡ recᴰ tᴰ
          |recFMᴰ|-η (|FreeModelᴰ|.var xᴰ) = refl
          |recFMᴰ|-η (|FreeModelᴰ|.app
            op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩) =
            app-η op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩
              (λ v → |recFMᴰ|-η (γᴰ v))
          |recFMᴰ|-η (|FreeModelᴰ|.freeAlg e t ρ ρᴰ) =
            freeAlg-η e t ρ ρᴰ (λ v → |recFMᴰ|-η (ρᴰ v))
          |recFMᴰ|-η (|FreeModelᴰ|.freeAlgEqn e ρ ρᴰ i) =
            isOfHLevel→isOfHLevelDep 1 {B = ηType} ηIsProp
              (freeAlg-η e (lhs e) ρ ρᴰ
                (λ v → |recFMᴰ|-η (ρᴰ v)))
              (freeAlg-η e (rhs e) ρ ρᴰ
                (λ v → |recFMᴰ|-η (ρᴰ v)))
              (λ k →
                |FreeModel|.freeAlgEqn e ρ k
                , |FreeModelᴰ|.freeAlgEqn e ρ ρᴰ k)
              i
          |recFMᴰ|-η (|FreeModelᴰ|.freeAlg-var e v ρ ρᴰ i) =
            isOfHLevel→isOfHLevelDep 1 {B = ηType} ηIsProp
              (|recFMᴰ|-η (ρᴰ v))
              (freeAlg-η e (S.var v) ρ ρᴰ
                (λ x → |recFMᴰ|-η (ρᴰ x)))
              (λ k →
                |FreeModel|.freeAlg-var e v ρ k
                , |FreeModelᴰ|.freeAlg-var e v ρ ρᴰ k)
              i
          |recFMᴰ|-η (|FreeModelᴰ|.freeAlg-op e op γ ρ ρᴰ i) =
            isOfHLevel→isOfHLevelDep 1 {B = ηType} ηIsProp
              (app-η op
                (λ v → |FreeModel|.freeAlg e (γ v) ρ)
                (λ v → |FreeModelᴰ|.freeAlg e (γ v) ρ ρᴰ)
                (|FreeModel|.app op
                  (λ v → |FreeModel|.freeAlg e (γ v) ρ))
                refl
                (λ v →
                  freeAlg-η e (γ v) ρ ρᴰ
                    (λ x → |recFMᴰ|-η (ρᴰ x))))
              (freeAlg-η e (S.app op γ) ρ ρᴰ
                (λ x → |recFMᴰ|-η (ρᴰ x)))
              (λ k →
                |FreeModel|.freeAlg-op e op γ ρ k
                , |FreeModelᴰ|.freeAlg-op e op γ ρ ρᴰ k)
              i
          |recFMᴰ|-η (|FreeModelᴰ|.isSetFreeModel
            xᴰ yᴰ pᴰ qᴰ i j) =
            isOfHLevel→isOfHLevelDep 2 {B = ηType}
              (λ z → isProp→isSet (ηIsProp z))
              (|recFMᴰ|-η xᴰ) (|recFMᴰ|-η yᴰ)
              (λ k → |recFMᴰ|-η (pᴰ k))
              (λ k → |recFMᴰ|-η (qᴰ k))
              (λ k l →
                |FreeModel|.isSetFreeModel _ _ _ _ k l
                , |FreeModelᴰ|.isSetFreeModel xᴰ yᴰ pᴰ qᴰ k l)
              i j

        recFMᴰ-η : ϕᴰ .fst ≡ recFMᴰ {A = A} ϕ Aᴰ ıᴰ .fst
        recFMᴰ-η =
          funExt λ t → funExt λ tᴰ → |recFMᴰ|-η tᴰ
