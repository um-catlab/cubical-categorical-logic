-- A Theory is a Signature extended with equational axioms.
-- A model of a theory is an algebra of the signature that satisfies the axioms.
--
-- Includes also displayed models and some constructions on (displayed) models.
module Cubical.Algebra.Theory.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.More
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Unit

open import Cubical.Algebra.Signature.Base public

private
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

  ModelStructure : hSet ℓ → Type _
  ModelStructure X =
    Σ[ A ∈ AlgebraWithCarrier ⟨ X ⟩ ] IsModel (⟨ X ⟩ , A)

  Model : ∀ ℓ → Type _
  Model ℓ = Σ[ X ∈ hSet ℓ ] ModelStructure X

  Model→Algebra : Model ℓ → Algebra ℓ
  Model→Algebra M = ⟨ M .fst ⟩ , M .snd .fst

  -- America's Next...
  ⊤Model : Model ℓ-zero
  ⊤Model .fst = Unit , isSetUnit
  ⊤Model .snd .fst = ⊤Algebra
  ⊤Model .snd .snd e ρ = refl

  ⊤*Model : Model ℓ
  ⊤*Model .fst = Unit* , isSetUnit*
  ⊤*Model .snd .fst = ⊤*Algebra
  ⊤*Model .snd .snd e ρ = refl

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
  Algebraᴰ-op-filler {A = A} Aᴰ f ρ ρᴰ f⟨ρ⟩ f∘ρ≡f⟨ρ⟩ i =
    f∘ρ≡f⟨ρ⟩ i , Aᴰ .snd f ρ ρᴰ (f∘ρ≡f⟨ρ⟩ i) (λ j → f∘ρ≡f⟨ρ⟩ (i ∧ j))

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

  IsModelᴰ : (M : Model ℓ) → Algebraᴰ (Model→Algebra M) ℓᴰ → Type _
  IsModelᴰ M Aᴰ =
    ∀ e (ρ : EqArity e → ⟨ M .fst ⟩)
      (ρᴰ : (v : EqArity e) → Aᴰ .fst (ρ v))
    → PathP (λ i → Aᴰ .fst (M .snd .snd e ρ i))
        (interpᴰ Aᴰ ρ ρᴰ (lhs e))
        (interpᴰ Aᴰ ρ ρᴰ (rhs e))

  ModelᴰWithCarrier : (M : Model ℓ)
    → (⟨ M .fst ⟩ → Type ℓᴰ) → Type _
  ModelᴰWithCarrier M Xᴰ =
    Σ[ αᴰ ∈ AlgebraᴰWithCarrier (Model→Algebra M) Xᴰ ]
      IsModelᴰ M (Xᴰ , αᴰ)

  Modelᴰ : Model ℓ → ∀ ℓᴰ → Type _
  Modelᴰ M ℓᴰ = Σ[ Xᴰ ∈ (⟨ M .fst ⟩ → hSet ℓᴰ) ]
    ModelᴰWithCarrier M (λ a → ⟨ Xᴰ a ⟩)

  Modelᴰ→Algebraᴰ : (M : Model ℓ)
    → Modelᴰ M ℓᴰ → Algebraᴰ (Model→Algebra M) ℓᴰ
  Modelᴰ→Algebraᴰ M Mᴰ = (λ a → ⟨ Mᴰ .fst a ⟩) , Mᴰ .snd .fst

  isPropIsModelᴰ : (M : Model ℓ) (Xᴰ : ⟨ M .fst ⟩ → hSet ℓᴰ)
    (αᴰ : AlgebraᴰWithCarrier (Model→Algebra M) (λ a → ⟨ Xᴰ a ⟩))
    → isProp (IsModelᴰ M (_ , αᴰ))
  isPropIsModelᴰ M Xᴰ αᴰ p q i e ρ ρᴰ =
    isOfHLevelPathP' 1 (Xᴰ _ .snd) _ _ (p e ρ ρᴰ) (q e ρ ρᴰ) i

  Modelᴰ≡ : {M : Model ℓ} {Mᴰ Nᴰ : Modelᴰ M ℓᴰ}
    → Modelᴰ→Algebraᴰ M Mᴰ ≡ Modelᴰ→Algebraᴰ M Nᴰ → Mᴰ ≡ Nᴰ
  Modelᴰ≡ {M = M} {Mᴰ = Mᴰ} {Nᴰ = Nᴰ} p =
    ΣPathP
      ( Xᴰ≡
      , ΣPathPProp (λ αᴰ → isPropIsModelᴰ M (Nᴰ .fst) αᴰ)
          (λ i → p i .snd))
    where
    Xᴰ≡ : Mᴰ .fst ≡ Nᴰ .fst
    Xᴰ≡ i a .fst = p i .fst a
    Xᴰ≡ i a .snd =
      isProp→PathP (λ j → isPropIsSet {A = p j .fst a})
        (Mᴰ .fst a .snd) (Nᴰ .fst a .snd) i

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
  ∫Model {M = M} Mᴰ .fst .fst = Σ[ a ∈ ⟨ M .fst ⟩ ] ⟨ Mᴰ .fst a ⟩
  ∫Model {M = M} Mᴰ .fst .snd =
    isSetΣ (M .fst .snd) (λ a → Mᴰ .fst a .snd)
  ∫Model {M = M} Mᴰ .snd .fst = ∫Algebra (Modelᴰ→Algebraᴰ M Mᴰ) .snd
  ∫Model {M = M} Mᴰ .snd .snd e ρ =
    interp∫ {A = Model→Algebra M} {Aᴰ = Modelᴰ→Algebraᴰ M Mᴰ} ρ (lhs e)
    ∙ ΣPathP
        ( M .snd .snd e (λ v → ρ v .fst)
        , Mᴰ .snd .snd e (λ v → ρ v .fst) (λ v → ρ v .snd))
    ∙ sym
        (interp∫ {A = Model→Algebra M} {Aᴰ = Modelᴰ→Algebraᴰ M Mᴰ}
          ρ (rhs e))

  module _ {M : Model ℓ} where
    Modelᴰᴰ : (Mᴰ : Modelᴰ M ℓᴰ) → ∀ ℓᴰᴰ → Type _
    Modelᴰᴰ Mᴰ ℓᴰᴰ = Modelᴰ (∫Model {M = M} Mᴰ) ℓᴰᴰ

    private
      ∫ᴰAlg : {Mᴰ : Modelᴰ M ℓᴰ} (Mᴰᴰ : Modelᴰᴰ Mᴰ ℓᴰᴰ)
        → Algebraᴰ (Model→Algebra M) _
      ∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ =
        S.∫ᴰAlgebra {A = Model→Algebra M} {Aᴰ = Modelᴰ→Algebraᴰ M Mᴰ}
          (Modelᴰ→Algebraᴰ (∫Model {M = M} Mᴰ) Mᴰᴰ)

    ∫ᴰModel-assoc : {Mᴰ : Modelᴰ M ℓᴰ}
      (Mᴰᴰ : Modelᴰᴰ Mᴰ ℓᴰᴰ)
      → ∫Algebra (Modelᴰ→Algebraᴰ (∫Model {M = M} Mᴰ) Mᴰᴰ) .fst
      → ∫Algebra (∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ) .fst
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .fst = z .fst .fst
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .snd .fst = z .fst .snd
    ∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ z .snd .snd = z .snd

    ∫ᴰModel-assocHomo : {Mᴰ : Modelᴰ M ℓᴰ}
      (Mᴰᴰ : Modelᴰᴰ Mᴰ ℓᴰᴰ)
      → S.Homo
          (∫Algebra (Modelᴰ→Algebraᴰ (∫Model {M = M} Mᴰ) Mᴰᴰ))
          (∫Algebra (∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ))
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
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .fst a .fst =
      Σ[ aᴰ ∈ ⟨ Mᴰ .fst a ⟩ ] ⟨ Mᴰᴰ .fst (a , aᴰ) ⟩
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .fst a .snd =
      isSetΣ (Mᴰ .fst a .snd) (λ aᴰ → Mᴰᴰ .fst (a , aᴰ) .snd)
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .snd .fst = ∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ .snd
    ∫ᴰModel {Mᴰ = Mᴰ} Mᴰᴰ .snd .snd e ρ ρᴰ =
      hSetReasoning.rectifyOut
        (M .fst)
        (∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ .fst)
        ( sym
            (interp∫
              {A = Model→Algebra M}
              {Aᴰ = ∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ}
              (λ v → ρ v , ρᴰ v) (lhs e))
        ∙ interpHomo
            (∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ)
            (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd)
            (lhs e)
        ∙ cong (∫ᴰModel-assoc {Mᴰ = Mᴰ} Mᴰᴰ)
            (∫Model
              {M = ∫Model {M = M} Mᴰ} Mᴰᴰ .snd .snd e
              (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd))
        ∙ sym
            (interpHomo
              (∫ᴰModel-assocHomo {Mᴰ = Mᴰ} Mᴰᴰ)
              (λ v → (ρ v , ρᴰ v .fst) , ρᴰ v .snd)
              (rhs e))
        ∙ interp∫
            {A = Model→Algebra M}
            {Aᴰ = ∫ᴰAlg {Mᴰ = Mᴰ} Mᴰᴰ}
            (λ v → ρ v , ρᴰ v) (rhs e))

  interpᴰwk : (M : Model ℓ) (N : Model ℓ') {V : Type ℓ''}
    (ρ : V → ⟨ M .fst ⟩) (ρᴰ : V → ⟨ N .fst ⟩) (t : |FreeAlgebra| V)
    → interpᴰ (wkAlg (Model→Algebra M) (Model→Algebra N)) ρ ρᴰ t
      ≡ interp (Model→Algebra N) ρᴰ t
  interpᴰwk M N ρ ρᴰ (var v) = refl
  interpᴰwk M N ρ ρᴰ (app f γ) =
    cong (N .snd .fst f) (funExt λ v → interpᴰwk M N ρ ρᴰ (γ v))
    ∙ recFA (Model→Algebra N) ρᴰ .snd f γ (app f γ) refl

  wkModel : (M : Model ℓ) (N : Model ℓ') → Modelᴰ M ℓ'
  wkModel M N .fst _ = N .fst
  wkModel M N .snd .fst =
    wkAlg (Model→Algebra M) (Model→Algebra N) .snd
  wkModel M N .snd .snd e ρ ρᴰ =
    interpᴰwk M N ρ ρᴰ (lhs e)
    ∙ N .snd .snd e ρᴰ
    ∙ sym (interpᴰwk M N ρ ρᴰ (rhs e))

  _×Model_ : (M : Model ℓ) (N : Model ℓ') → Model _
  M ×Model N = ∫Model {M = M} (wkModel M N)

  -- Powering a model by a type
  module _ (A : Type ℓ') (B : Model ℓ) where
    PowerAlgebra : Algebra (ℓ-max ℓ' ℓ)
    PowerAlgebra .fst = A → ⟨ B .fst ⟩
    PowerAlgebra .snd op γ x = B .snd .fst op (λ v → γ v x)

    evalPower : (x : A) → S.Homo PowerAlgebra (Model→Algebra B)
    evalPower x .fst f = f x
    evalPower x .snd op γ op⟨γ⟩ p i = p i x

    PowerModel : Model (ℓ-max ℓ' ℓ)
    PowerModel .fst = (A → ⟨ B .fst ⟩) , isSetΠ (λ _ → B .fst .snd)
    PowerModel .snd .fst = PowerAlgebra .snd
    PowerModel .snd .snd e γ = funExt λ x →
      sym (interpHomo (evalPower x) γ (lhs e))
      ∙ B .snd .snd e (λ v → γ v x)
      ∙ interpHomo (evalPower x) γ (rhs e)

    -- Displayed Powering
    module _ (Aᴰ : A → Type ℓᴰ') (Bᴰ : Modelᴰ B ℓᴰ) where
      PowerAlgebraᴰ : Algebraᴰ PowerAlgebra (ℓ-max (ℓ-max ℓ' ℓᴰ') ℓᴰ)
      PowerAlgebraᴰ .fst f = (x : A) → Aᴰ x → ⟨ Bᴰ .fst (f x) ⟩
      PowerAlgebraᴰ .snd op γ γᴰ op⟨γ⟩ p x xᴰ =
        Bᴰ .snd .fst op (λ v → γ v x) (λ v → γᴰ v x xᴰ)
          (op⟨γ⟩ x) (λ i → p i x)

      interpPowerᴰ : {V : Type ℓ''}
        (ρ : V → PowerAlgebra .fst)
        (ρᴰ : (v : V) → PowerAlgebraᴰ .fst (ρ v))
        (t : |FreeAlgebra| V) (x : A) (xᴰ : Aᴰ x)
        → interpᴰ PowerAlgebraᴰ ρ ρᴰ t x xᴰ
          ≡ interpᴰ (evalPower x S.* Modelᴰ→Algebraᴰ B Bᴰ)
              ρ (λ v → ρᴰ v x xᴰ) t
      interpPowerᴰ ρ ρᴰ (var v) x xᴰ = refl
      interpPowerᴰ ρ ρᴰ (app op γ) x xᴰ =
        cong
          (λ γᴰ → Bᴰ .snd .fst op
            (λ v → interp PowerAlgebra ρ (γ v) x) γᴰ
            (interp PowerAlgebra ρ (app op γ) x)
            (λ i → recFA PowerAlgebra ρ .snd
              op γ (app op γ) refl i x))
          (funExt λ v → interpPowerᴰ ρ ρᴰ (γ v) x xᴰ)

      PowerModelᴰ : Modelᴰ PowerModel (ℓ-max (ℓ-max ℓ' ℓᴰ') ℓᴰ)
      PowerModelᴰ .fst f =
        PowerAlgebraᴰ .fst f , isSetΠ2 λ x _ → Bᴰ .fst (f x) .snd
      PowerModelᴰ .snd .fst = PowerAlgebraᴰ .snd
      PowerModelᴰ .snd .snd e ρ ρᴰ i x xᴰ =
        hSetReasoning.rectifyOut (B .fst) (λ b → ⟨ Bᴰ .fst b ⟩)
          {e' = cong (λ f → f x) (PowerModel .snd .snd e ρ)}
          ( (λ j →
              interp PowerAlgebra ρ (lhs e) x
              , interpPowerᴰ ρ ρᴰ (lhs e) x xᴰ j)
          ∙ sym (interpPullback (evalPower x)
              (Modelᴰ→Algebraᴰ B Bᴰ) ρ (λ v → ρᴰ v x xᴰ) (lhs e))
          ∙ ΣPathP
              ( B .snd .snd e (λ v → ρ v x)
              , Bᴰ .snd .snd e (λ v → ρ v x)
                  (λ v → ρᴰ v x xᴰ))
          ∙ interpPullback (evalPower x)
              (Modelᴰ→Algebraᴰ B Bᴰ) ρ (λ v → ρᴰ v x xᴰ) (rhs e)
          ∙ (λ j →
              interp PowerAlgebra ρ (rhs e) x
              , interpPowerᴰ ρ ρᴰ (rhs e) x xᴰ (~ j))) i

  -- Pullback of a displayed model
  module _ {M : Model ℓ} {N : Model ℓ'} where
    _*_ : S.Homo (Model→Algebra M) (Model→Algebra N)
      → Modelᴰ N ℓᴰ → Modelᴰ M ℓᴰ
    (ϕ * Nᴰ) .fst a = Nᴰ .fst (ϕ .fst a)
    (ϕ * Nᴰ) .snd .fst = (ϕ S.* Modelᴰ→Algebraᴰ N Nᴰ) .snd
    (ϕ * Nᴰ) .snd .snd e ρ ρᴰ =
      hSetReasoning.rectifyOut
        (N .fst) (λ a → ⟨ Nᴰ .fst a ⟩)
        ( sym (interpPullback ϕ (Modelᴰ→Algebraᴰ N Nᴰ) ρ ρᴰ (lhs e))
        ∙ ΣPathP
            ( N .snd .snd e (λ v → ϕ .fst (ρ v))
            , Nᴰ .snd .snd e (λ v → ϕ .fst (ρ v)) ρᴰ)
        ∙ interpPullback ϕ (Modelᴰ→Algebraᴰ N Nᴰ) ρ ρᴰ (rhs e))

  -- Every homomorphism h : M → N makes M a model displayed over N, with
  -- the fibres of h as fibres.  Together with ∫Model this is the
  -- equivalence between models over N and displayed models over N.
  module _ {M : Model ℓ} {N : Model ℓ'}
    (h : S.Homo (Model→Algebra M) (Model→Algebra N)) where

    FiberAlgebraᴰ : Algebraᴰ (Model→Algebra N) (ℓ-max ℓ ℓ')
    FiberAlgebraᴰ .fst = fiber (h .fst)
    FiberAlgebraᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      M .snd .fst op (fst ∘ γᴰ)
      , sym (h .snd op (fst ∘ γᴰ) _ refl)
        ∙ cong (N .snd .fst op) (funExt (snd ∘ γᴰ))
        ∙ op∘γ≡op⟨γ⟩

    private
      interpFiber-fst : {V : Type ℓ''} (ρ : V → ⟨ N .fst ⟩)
        (ρᴰ : (v : V) → fiber (h .fst) (ρ v)) (t : |FreeAlgebra| V)
        → interpᴰ FiberAlgebraᴰ ρ ρᴰ t .fst
          ≡ interp (Model→Algebra M) (fst ∘ ρᴰ) t
      interpFiber-fst ρ ρᴰ (var v) = refl
      interpFiber-fst ρ ρᴰ (app op γ) =
        cong (M .snd .fst op) (funExt λ v → interpFiber-fst ρ ρᴰ (γ v))

    FiberModelᴰ : Modelᴰ N (ℓ-max ℓ ℓ')
    FiberModelᴰ .fst n =
      fiber (h .fst) n
      , isSetΣ (M .fst .snd) (λ _ → isProp→isSet (N .fst .snd _ _))
    FiberModelᴰ .snd .fst = FiberAlgebraᴰ .snd
    FiberModelᴰ .snd .snd e ρ ρᴰ = ΣPathP
      ( interpFiber-fst ρ ρᴰ (lhs e)
        ∙ M .snd .snd e (fst ∘ ρᴰ)
        ∙ sym (interpFiber-fst ρ ρᴰ (rhs e))
      , isProp→PathP (λ i → N .fst .snd _ _) _ _)

    -- Its universal property: a displayed homomorphism out of the fibres
    -- over ψ is a section of the pullback of the target along h ⋆ ψ.
    module _ {Z : Model ℓ''}
      (ψ : S.Homo (Model→Algebra N) (Model→Algebra Z))
      (Zᴰ : Modelᴰ Z ℓᴰ) where
      private
        hψ : S.Homo (Model→Algebra M) (Model→Algebra Z)
        hψ = S._⋆H_ {C = Model→Algebra Z} h ψ

        Fibᴰ = Modelᴰ→Algebraᴰ N FiberModelᴰ
        Zᴰ' = Modelᴰ→Algebraᴰ Z Zᴰ
        module ZᴰR = hSetReasoning (Z .fst) (λ z → ⟨ Zᴰ .fst z ⟩)

      fiberᴰ-restrict : S.Homoᴰ ψ Fibᴰ Zᴰ'
        → S.Section (Modelᴰ→Algebraᴰ M (_*_ {M = M} {N = Z} hψ Zᴰ))
      fiberᴰ-restrict χᴰ .fst m = χᴰ .fst (h .fst m) (m , refl)
      fiberᴰ-restrict χᴰ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
        χᴰ .snd op (h .fst ∘ γ) (λ v → γ v , refl) (h .fst op⟨γ⟩)
          (h .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩) (op⟨γ⟩ , refl)
          (ΣPathP (op∘γ≡op⟨γ⟩ , isProp→PathP (λ i → N .fst .snd _ _) _ _))

      fiberᴰ-intro : S.Section (Modelᴰ→Algebraᴰ M (_*_ {M = M} {N = Z} hψ Zᴰ))
        → S.Homoᴰ ψ Fibᴰ Zᴰ'
      fiberᴰ-intro σ .fst n (m , p) = ZᴰR.reind (cong (ψ .fst) p) (σ .fst m)
      fiberᴰ-intro σ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ op⟨γᴰ⟩ op∘γᴰ≡op⟨γᴰ⟩ =
        ZᴰR.rectifyOut $
          sym (Algebraᴰ-op-filler Zᴰ' op (ψ .fst ∘ γ)
            (λ v → fiberᴰ-intro σ .fst (γ v) (γᴰ v)) _
            (ψ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩))
          ∙ sym (cong (∫Algebra Zᴰ' .snd op)
              (funExt λ v → ZᴰR.reind-filler (cong (ψ .fst) (γᴰ v .snd))))
          ∙ Algebraᴰ-op-filler Zᴰ' op (ψ .fst ∘ h .fst ∘ fst ∘ γᴰ)
              (σ .fst ∘ fst ∘ γᴰ) _ (hψ .snd op (fst ∘ γᴰ) _ refl)
          ∙ ZᴰR.≡in (σ .snd op (fst ∘ γᴰ) _ refl)
          ∙ ZᴰR.reind-filler
              (cong (ψ .fst) (FiberAlgebraᴰ .snd op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ .snd))
          ∙ ZᴰR.≡in (cong (fiberᴰ-intro σ .fst op⟨γ⟩) op∘γᴰ≡op⟨γᴰ⟩)

      fiberᴰ-β : ∀ σ → fiberᴰ-restrict (fiberᴰ-intro σ) ≡ σ
      fiberᴰ-β σ = Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → Zᴰ .fst _ .snd _ _)
        (funExt λ m → ZᴰR.rectifyOut (ZᴰR.reind-filler⁻ refl))

      fiberᴰ-η : ∀ χᴰ → fiberᴰ-intro (fiberᴰ-restrict χᴰ) ≡ χᴰ
      fiberᴰ-η χᴰ = Σ≡Prop
        (λ _ → isPropΠ6 λ _ _ _ _ _ _ → isPropΠ λ _ → Zᴰ .fst _ .snd _ _)
        (funExt λ n → funExt λ (m , p) →
          ZᴰR.rectifyOut
            ( ZᴰR.reind-filler⁻ (cong (ψ .fst) p)
            ∙ cong totalχ (ΣPathP (p , ΣPathP (refl , λ i j → p (i ∧ j))))))
        where
        totalχ : Σ ⟨ N .fst ⟩ (fiber (h .fst))
          → Σ ⟨ Z .fst ⟩ (λ z → ⟨ Zᴰ .fst z ⟩)
        totalχ q = ψ .fst (q .fst) , χᴰ .fst (q .fst) (q .snd)

  module _ {M : Model ℓ} {Mᴰ : Modelᴰ M ℓᴰ} where
    *Id : _*_ {M = M} {N = M} (S.idHomo {A = Model→Algebra M}) Mᴰ ≡ Mᴰ
    *Id = Modelᴰ≡ {M = M}
      (S.*Id {A = Model→Algebra M} {Aᴰ = Modelᴰ→Algebraᴰ M Mᴰ})

  module _ {M : Model ℓ} {N : Model ℓ'} {P : Model ℓ''}
    {Pᴰ : Modelᴰ P ℓᴰ''}
    (ϕ : S.Homo (Model→Algebra M) (Model→Algebra N))
    (ψ : S.Homo (Model→Algebra N) (Model→Algebra P)) where
    *∘ : _*_ {M = M} {N = P}
          (S._⋆H_ {A = Model→Algebra M} {B = Model→Algebra N}
            {C = Model→Algebra P} ϕ ψ) Pᴰ
        ≡ _*_ {M = M} {N = N} ϕ
            (_*_ {M = N} {N = P} ψ Pᴰ)
    *∘ = Modelᴰ≡ {M = M}
      (S.*∘
        {A = Model→Algebra M} {B = Model→Algebra N}
        {C = Model→Algebra P} {Cᴰ = Modelᴰ→Algebraᴰ P Pᴰ}
        ϕ ψ)

  -- Path as a displayed Model
  module _ (M : Model ℓ) where
    PathModel : Modelᴰ (M ×Model M) ℓ
    PathModel .fst (m , n) = (m ≡ n) , isProp→isSet (M .fst .snd m n)
    PathModel .snd .fst = S.PathAlg (Model→Algebra M) .snd
    PathModel .snd .snd e ρ ρᴰ =
      isProp→PathP (λ _ → M .fst .snd _ _)
        (interpᴰ (S.PathAlg (Model→Algebra M)) ρ ρᴰ (lhs e))
        (interpᴰ (S.PathAlg (Model→Algebra M)) ρ ρᴰ (rhs e))

    PathModelReflection : {Γ : Model ℓ'}
      (ϕ ψ : S.Homo (Model→Algebra Γ) (Model→Algebra M))
      → S.Section
          (S._*_
            {A = Model→Algebra Γ} {B = Model→Algebra (M ×Model M)}
            (S.×intro
              {Γ = Model→Algebra Γ} {A = Model→Algebra M}
              {B = Model→Algebra M} ϕ ψ)
            (Modelᴰ→Algebraᴰ (M ×Model M) PathModel))
      → ϕ .fst ≡ ψ .fst
    PathModelReflection {Γ = Γ} ϕ ψ ϕ≡ψ =
      S.PathAlgReflection (Model→Algebra M)
        {Γ = Model→Algebra Γ} ϕ ψ ϕ≡ψ

  -- Paths between two sections of a displayed model, as a displayed
  -- model with propositional fibres.
  module _ {M : Model ℓ} (Mᴰ : Modelᴰ M ℓᴰ)
    (σ τ : S.Section (Modelᴰ→Algebraᴰ M Mᴰ)) where
    SectionPathModelᴰ : Modelᴰ M ℓᴰ
    SectionPathModelᴰ .fst m =
      (σ .fst m ≡ τ .fst m) , isProp→isSet (Mᴰ .fst m .snd _ _)
    SectionPathModelᴰ .snd .fst op γ γᴰ op⟨γ⟩ op∘γ≡op⟨γ⟩ =
      sym (σ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩)
      ∙ cong (λ s → Mᴰ .snd .fst op γ s op⟨γ⟩ op∘γ≡op⟨γ⟩) (funExt γᴰ)
      ∙ τ .snd op γ op⟨γ⟩ op∘γ≡op⟨γ⟩
    SectionPathModelᴰ .snd .snd e ρ ρᴰ =
      isProp→PathP (λ _ → Mᴰ .fst _ .snd _ _) _ _

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
    FreeModel .fst = |FreeModel| , isSetFreeModel
    FreeModel .snd .fst = app
    FreeModel .snd .snd e γ =
      freeAlg≡recFA e (lhs e) γ
      ∙ freeAlgEqn e γ
      ∙ (sym $ freeAlg≡recFA e (rhs e) γ)

    module _ (Bᴰ : Modelᴰ FreeModel ℓᴰ) where
      private
        module BᴰReasoning =
          hSetReasoning (FreeModel .fst) (λ t → ⟨ Bᴰ .fst t ⟩)

      freeAlgᴰ : ∀ e (t : |FreeAlgebra| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → ⟨ Bᴰ .fst (ρ v) ⟩)
        → ⟨ Bᴰ .fst (freeAlg e t ρ) ⟩
      freeAlgᴰ e t ρ ρᴰ =
        BᴰReasoning.reind (freeAlg≡recFA e t ρ)
          (interpᴰ (Modelᴰ→Algebraᴰ FreeModel Bᴰ) ρ ρᴰ t)

      freeAlgᴰ-filler : ∀ e (t : |FreeAlgebra| (EqArity e))
        (ρ : EqArity e → |FreeModel|)
        (ρᴰ : (v : EqArity e) → ⟨ Bᴰ .fst (ρ v) ⟩)
        → Path (∫Algebra (Modelᴰ→Algebraᴰ FreeModel Bᴰ) .fst)
            ( interp FreeModelAlgebra ρ t
            , interpᴰ (Modelᴰ→Algebraᴰ FreeModel Bᴰ) ρ ρᴰ t)
            (freeAlg e t ρ , freeAlgᴰ e t ρ ρᴰ)
      freeAlgᴰ-filler e t ρ ρᴰ =
        BᴰReasoning.reind-filler (freeAlg≡recFA e t ρ)

      module _ (ı : (x : X) → ⟨ Bᴰ .fst (|FreeModel|.var x) ⟩) where
        elimFreeModelfun : (t : |FreeModel|) → ⟨ Bᴰ .fst t ⟩
        elimFreeModelfun (var x) = ı x
        elimFreeModelfun (app op γ) =
          Bᴰ .snd .fst op γ (λ v → elimFreeModelfun (γ v))
            (app op γ) refl
        elimFreeModelfun (freeAlg e t ρ) =
          freeAlgᴰ e t ρ (λ v → elimFreeModelfun (ρ v))
        elimFreeModelfun (freeAlgEqn e ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlgEqn e ρ}
            ( sym
                (freeAlgᴰ-filler e (lhs e) ρ
                  (λ v → elimFreeModelfun (ρ v)))
            ∙ BᴰReasoning.≡in
                (Bᴰ .snd .snd e ρ (λ v → elimFreeModelfun (ρ v)))
            ∙ freeAlgᴰ-filler e (rhs e) ρ
                (λ v → elimFreeModelfun (ρ v))) i
        elimFreeModelfun (freeAlg-var e v ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlg-var e v ρ}
            (freeAlgᴰ-filler e (var v) ρ
              (λ x → elimFreeModelfun (ρ x))) i
        elimFreeModelfun (freeAlg-op e op γ ρ i) =
          BᴰReasoning.rectifyOut {e' = freeAlg-op e op γ ρ}
            ( sym
                (cong (∫Algebra (Modelᴰ→Algebraᴰ FreeModel Bᴰ) .snd op)
                  (funExt λ v →
                    freeAlgᴰ-filler e (γ v) ρ
                      (λ x → elimFreeModelfun (ρ x))))
            ∙ Algebraᴰ-op-filler (Modelᴰ→Algebraᴰ FreeModel Bᴰ) op
                (λ v → interp FreeModelAlgebra ρ (γ v))
                (λ v →
                  interpᴰ (Modelᴰ→Algebraᴰ FreeModel Bᴰ) ρ
                    (λ x → elimFreeModelfun (ρ x)) (γ v))
                (interp FreeModelAlgebra ρ (app op γ))
                (recFA FreeModelAlgebra ρ .snd op γ (app op γ) refl)
            ∙ freeAlgᴰ-filler e (app op γ) ρ
                (λ x → elimFreeModelfun (ρ x))) i
        elimFreeModelfun (isSetFreeModel x y p q i j) =
          isSet→isSetDep (λ t → Bᴰ .fst t .snd)
            (elimFreeModelfun x) (elimFreeModelfun y)
            (cong elimFreeModelfun p) (cong elimFreeModelfun q)
            (isSetFreeModel x y p q) i j

        elimFreeModel : S.Section (Modelᴰ→Algebraᴰ FreeModel Bᴰ)
        elimFreeModel .fst = elimFreeModelfun
        elimFreeModel .snd f γ f⟨γ⟩ f∘γ≡f⟨γ⟩ =
          J (λ f⟨γ⟩ f∘γ≡f⟨γ⟩ →
              Bᴰ .snd .fst f γ (λ v → elimFreeModelfun (γ v))
                  f⟨γ⟩ f∘γ≡f⟨γ⟩
                ≡ elimFreeModelfun f⟨γ⟩)
            refl f∘γ≡f⟨γ⟩

    -- Sections over the free model are determined by their values on
    -- generators.
    module _ (Bᴰ : Modelᴰ FreeModel ℓᴰ)
      (σ : S.Section (Modelᴰ→Algebraᴰ FreeModel Bᴰ)) where
      elimFreeModel-uniq : σ ≡ elimFreeModel Bᴰ (λ x → σ .fst (var x))
      elimFreeModel-uniq = Σ≡Prop
        (λ _ → isPropΠ4 λ _ _ _ _ → Bᴰ .fst _ .snd _ _)
        (funExt (elimFreeModel
          (SectionPathModelᴰ {M = FreeModel} Bᴰ σ
            (elimFreeModel Bᴰ (λ x → σ .fst (var x))))
          (λ _ → refl) .fst))

    module _ (B : Model ℓ') where
      recFM : (X → ⟨ B .fst ⟩)
        → S.Homo FreeModelAlgebra (Model→Algebra B)
      recFM ı = elimFreeModel (wkModel FreeModel B) ı

      recFM-uniq : (f : S.Homo FreeModelAlgebra (Model→Algebra B))
        → f .fst ≡ recFM (f .fst ∘ var) .fst
      recFM-uniq f =
        PathModelReflection B {Γ = FreeModel} f g
          (elimFreeModel
            (_*_ {M = FreeModel} {N = B ×Model B}
              (S.×intro
                {Γ = FreeModelAlgebra} {A = Model→Algebra B}
                {B = Model→Algebra B} f g)
              (PathModel B))
            (λ _ → refl))
        where
        g : S.Homo FreeModelAlgebra (Model→Algebra B)
        g = recFM (f .fst ∘ var)
