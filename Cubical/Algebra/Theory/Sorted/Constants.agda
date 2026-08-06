-- Adjoining constants to a many-sorted theory
module Cubical.Algebra.Theory.Sorted.Constants where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure

open import Cubical.Data.Empty using (⊥; ⊥*)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Unit

open import Cubical.Categories.Category
open import Cubical.Categories.Limits.Initial

open import Cubical.Algebra.Theory.Sorted
open import Cubical.Algebra.Theory.Sorted.Constructions
open import Cubical.Algebra.Theory.Sorted.Free.Bind

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓw ℓX ℓa ℓb : Level

open SortedSig
open SortedEqns

private
  noArgs : {A : ⊥* {ℓ'} → Type ℓa} (a : ⊥* {ℓ'}) → A a
  noArgs ()

  noArgsη : {A : ⊥* {ℓ'} → Type ℓa} {B : Type ℓb}
    (h : ((a : ⊥* {ℓ'}) → A a) → B) (g : (a : ⊥* {ℓ'}) → A a)
    → h noArgs ≡ h g
  noArgsη h g = cong h (funExt (λ ()))

module _ {S : Type ℓS} where

  PointedSigᶠ : (X : S → Type ℓw) → SortedSig S (ℓ-max ℓS ℓw) ℓ'
  PointedSigᶠ X .ops = Σ[ s ∈ S ] X s
  PointedSigᶠ X .arities _ = ⊥*
  PointedSigᶠ X .sortOf _ ()
  PointedSigᶠ X .resultSort = fst

  -- no equations, so the variable level is unconstrained and can be
  -- taken to be whatever the theory being extended uses
  Pointedᶠ : (X : S → Type ℓw)
    → SortedEqns (PointedSigᶠ {ℓ' = ℓ'} X) ℓ-zero ℓv
  Pointedᶠ X .eqns = ⊥
  Pointedᶠ X .eqnSort ()
  Pointedᶠ X .vars ()
  Pointedᶠ X .varSort ()
  Pointedᶠ X .lhs ()
  Pointedᶠ X .rhs ()

-- Adjoining constants.  `σeq [ X ]adjoin` is σeq with a constant of
-- sort s adjoined for every element of X s: the coproduct of σeq with
-- the pointed theory on X.  The suffix is needed because `σeq [ X ]`
-- would clash with the hom notation `C [ c , c' ]`.
infixl 30 _[_]adjoin
_[_]adjoin : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (X : S → Type ℓw)
  → SortedEqns (σ ⊕Sig PointedSigᶠ X) ℓ'' ℓv
σeq [ X ]adjoin = σeq ⊕Eqns Pointedᶠ X

-- A model on a fixed carrier family: exactly `MODᴰ σeq ℓX`'s objects
-- over Y, spelled out.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  Sat : (σeq : SortedEqns σ ℓ'' ℓv) (Y : S → Type ℓX)
    → Ops {σ = σ} Y → Type _
  Sat σeq Y α = (e : σeq .eqns)
    (ρ : (v : σeq .vars e) → Y (σeq .varSort e v))
    → TmRec Y α ρ (σeq .lhs e) ≡ TmRec Y α ρ (σeq .rhs e)

  Model : (σeq : SortedEqns σ ℓ'' ℓv) (Y : S → hSet ℓX) → Type _
  Model σeq Y =
    Σ[ α ∈ Ops {σ = σ} (λ s → ⟨ Y s ⟩) ] Sat σeq (λ s → ⟨ Y s ⟩) α

  isPropSat : (σeq : SortedEqns σ ℓ'' ℓv) (Y : S → hSet ℓX)
    (α : Ops {σ = σ} (λ s → ⟨ Y s ⟩))
    → isProp (Sat σeq (λ s → ⟨ Y s ⟩) α)
  isPropSat σeq Y α = isPropΠ2 (λ e ρ → Y (σeq .eqnSort e) .snd _ _)

-- the points of a pointed algebra, and the pointed algebra on a family
-- of chosen elements
module _ {S : Type ℓS} (X : S → Type ℓw) (Y : S → Type ℓX) where

  pointsOfᶠ : Ops {σ = PointedSigᶠ {ℓ' = ℓ'} X} Y → (s : S) → X s → Y s
  pointsOfᶠ α s x = α (s , x) noArgs

  mkPointsᶠ : ((s : S) → X s → Y s) → Ops {σ = PointedSigᶠ {ℓ' = ℓ'} X} Y
  mkPointsᶠ ρ v _ = ρ (v .fst) (v .snd)

-- A model of `σeq [ X ]adjoin` is a model of σeq together with, at
-- each sort s, a map X s → carrier s.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (X : S → Type ℓw) where

  private
    P : SortedSig S (ℓ-max ℓS ℓw) ℓ'
    P = PointedSigᶠ X

  module _ (Y : S → hSet ℓX) where

    private
      ⟨Y⟩ : S → Type ℓX
      ⟨Y⟩ s = ⟨ Y s ⟩

    ⊕Ops : Ops {σ = σ} ⟨Y⟩ → ((s : S) → X s → ⟨Y⟩ s)
      → Ops {σ = σ ⊕Sig P} ⟨Y⟩
    ⊕Ops β ρ (inl o) = β o
    ⊕Ops β ρ (inr v) = mkPointsᶠ X ⟨Y⟩ ρ v

    ⊕Sat : (β : Ops {σ = σ} ⟨Y⟩) (ρ : (s : S) → X s → ⟨Y⟩ s)
      → Sat σeq ⟨Y⟩ β → Sat (σeq [ X ]adjoin) ⟨Y⟩ (⊕Ops β ρ)
    ⊕Sat β ρ sat (inl e) ρ' =
      TmRec-inl σ P ⟨Y⟩ (⊕Ops β ρ) ρ' (σeq .lhs e)
      ∙ sat e ρ'
      ∙ sym (TmRec-inl σ P ⟨Y⟩ (⊕Ops β ρ) ρ' (σeq .rhs e))

    modelIso : Iso (Model (σeq [ X ]adjoin) Y)
                   (Model σeq Y × ((s : S) → X s → ⟨Y⟩ s))
    modelIso .Iso.fun (α , sat) =
      ((λ o → α (inl o)) , satl σeq (Pointedᶠ X) ⟨Y⟩ α sat)
      , pointsOfᶠ X ⟨Y⟩ (resr σ P ⟨Y⟩ α)
    modelIso .Iso.inv ((β , sat) , ρ) = ⊕Ops β ρ , ⊕Sat β ρ sat
    modelIso .Iso.sec ((β , sat) , ρ) =
      ΣPathP (Σ≡Prop (isPropSat σeq Y) refl , refl)
    modelIso .Iso.ret (α , sat) =
      Σ≡Prop (isPropSat (σeq [ X ]adjoin) Y)
        (funExt (λ { (inl o) → refl
                   ; (inr v) → funExt (noArgsη (α (inr v))) }))

    withPoints : Model σeq Y → ((s : S) → X s → ⟨Y⟩ s)
      → Model (σeq [ X ]adjoin) Y
    withPoints M ρ = Iso.inv modelIso (M , ρ)

    forgetPoints : Model (σeq [ X ]adjoin) Y → Model σeq Y
    forgetPoints N = Iso.fun modelIso N .fst

    pointsAt : Model (σeq [ X ]adjoin) Y → (s : S) → X s → ⟨Y⟩ s
    pointsAt N = Iso.fun modelIso N .snd

module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' (ℓ-max ℓS ℓw)) (X : S → Type ℓw) where

  private
    V : Type (ℓ-max ℓS ℓw)
    V = Σ[ s ∈ S ] X s

    ℓF = ℓFree ℓS ℓ ℓ' ℓ'' (ℓ-max ℓS ℓw)

    FreeSet : S → hSet ℓF
    FreeSet s = FreeModel σeq V fst s , trunc

  FreeModelˢ[X] : Model (σeq [ X ]adjoin) FreeSet
  FreeModelˢ[X] =
    withPoints σeq X FreeSet (opF , FreeEqns σeq) (λ s x → gen (s , x))

  FreeObˢ[X] : Category.ob (MOD (σeq [ X ]adjoin) ℓF)
  FreeObˢ[X] = FreeSet , FreeModelˢ[X]

  module _ (N : Category.ob (MOD (σeq [ X ]adjoin) ℓF)) where
    private
      Y : S → Type ℓF
      Y s = ⟨ N .fst s ⟩

      isSetY : (s : S) → isSet (Y s)
      isSetY s = N .fst s .snd

      α = N .snd .fst
      β = forgetPoints σeq X (N .fst) (N .snd) .fst
      sat = forgetPoints σeq X (N .fst) (N .snd) .snd

      Nρ : (v : V) → Y (v .fst)
      Nρ v = pointsAt σeq X (N .fst) (N .snd) (v .fst) (v .snd)

    recC : (s : S) → FreeModel σeq V fst s → Y s
    recC _ = rec σeq isSetY β sat Nρ

    recHom : (o : (σ ⊕Sig PointedSigᶠ X) .ops)
      (x : (a : (σ ⊕Sig PointedSigᶠ X) .arities o)
         → FreeModel σeq V fst
             ((σ ⊕Sig PointedSigᶠ X) .sortOf o a))
      (y : FreeModel σeq V fst
             ((σ ⊕Sig PointedSigᶠ X) .resultSort o))
      → y ≡ FreeModelˢ[X] .fst o x
      → recC _ y ≡ α o (λ a → recC _ (x a))
    recHom (inl o) x y eq = cong (recC _) eq
    recHom (inr v) x y eq =
      cong (recC _) eq ∙ noArgsη (α (inr v)) (λ a → recC _ (x a))

    isContrHomˢ[X] :
      isContr (ModHom (σeq [ X ]adjoin) ℓF FreeObˢ[X] N)
    isContrHomˢ[X] .fst = recC , recHom , tt*
    isContrHomˢ[X] .snd (f , ϕ , _) =
      Σ≡Prop
        (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetY _ _ _))
                       (λ _ → isPropUnit*))
        (funExt (λ s → funExt (λ x →
          sym (recUniq σeq isSetY β sat Nρ f
                 (λ o → ϕ (inl o))
                 (λ v → ϕ (inr v) noArgs (gen v) refl
                        ∙ sym (noArgsη (α (inr v)) _))
                 x))))

  isInitialFreeObˢ[X] :
    isInitial (MOD (σeq [ X ]adjoin) ℓF) FreeObˢ[X]
  isInitialFreeObˢ[X] = isContrHomˢ[X]

  InitialMODˢ[X] : Initial (MOD (σeq [ X ]adjoin) ℓF)
  InitialMODˢ[X] = FreeObˢ[X] , isInitialFreeObˢ[X]
