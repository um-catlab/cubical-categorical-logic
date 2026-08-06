-- Adjoining constants to a many-sorted theory, and freeness as
-- initiality.
--
-- The free model on a sorted set (V , vs) is the initial model of
-- `σeq [ V , vs ]adjoin`, the theory σeq extended by one constant of
-- sort `vs v` for each `v : V`.  Coproduct rather than tensor is the
-- point: the generators are subject to no interaction with σ's
-- operations beyond σ's own equations.
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

private
  variable
    ℓS ℓ ℓ' ℓ'' ℓv ℓX ℓa ℓb : Level

open SortedSig
open SortedEqns

-- `⊥*` has no definitional η, so two separately elaborated absurd
-- lambdas are never definitionally equal.  Every argument tuple of a
-- constant is *this* one, and `noArgsη` is the bridge to any other.
private
  noArgs : {A : ⊥* {ℓ'} → Type ℓa} (a : ⊥* {ℓ'}) → A a
  noArgs ()

  noArgsη : {A : ⊥* {ℓ'} → Type ℓa} {B : Type ℓb}
    (h : ((a : ⊥* {ℓ'}) → A a) → B) (g : (a : ⊥* {ℓ'}) → A a)
    → h noArgs ≡ h g
  noArgsη h g = cong h (funExt (λ ()))

module _ {S : Type ℓS} where

  -- one constant of sort `vs v` for each `v : V`, and no equations
  PointedSigˢ : (V : Type ℓv) (vs : V → S) → SortedSig S ℓv ℓ'
  PointedSigˢ V vs .ops = V
  PointedSigˢ V vs .arities _ = ⊥*
  PointedSigˢ V vs .sortOf _ ()
  PointedSigˢ V vs .resultSort = vs

  Pointedˢ : (V : Type ℓv) (vs : V → S)
    → SortedEqns (PointedSigˢ {ℓ' = ℓ'} V vs) ℓ-zero ℓv
  Pointedˢ V vs .eqns = ⊥
  Pointedˢ V vs .eqnSort ()
  Pointedˢ V vs .vars ()
  Pointedˢ V vs .varSort ()
  Pointedˢ V vs .lhs ()
  Pointedˢ V vs .rhs ()

-- Adjoining constants.  `σeq [ V , vs ]adjoin` is σeq with a constant
-- adjoined for every element of the sorted set (V , vs): the coproduct
-- of σeq with the pointed theory on (V , vs).
infixl 30 _[_,_]adjoin
_[_,_]adjoin : {S : Type ℓS} {σ : SortedSig S ℓ ℓ'}
  (σeq : SortedEqns σ ℓ'' ℓv) (V : Type ℓv) (vs : V → S)
  → SortedEqns (σ ⊕Sig PointedSigˢ V vs) ℓ'' ℓv
σeq [ V , vs ]adjoin = σeq ⊕Eqns Pointedˢ V vs

-- A model on a fixed carrier family: exactly `MODᴰ σeq ℓX`'s objects
-- over X, spelled out.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} where

  Sat : (σeq : SortedEqns σ ℓ'' ℓv) (X : S → Type ℓX)
    → Ops {σ = σ} X → Type _
  Sat σeq X α = (e : σeq .eqns)
    (ρ : (v : σeq .vars e) → X (σeq .varSort e v))
    → TmRec X α ρ (σeq .lhs e) ≡ TmRec X α ρ (σeq .rhs e)

  Model : (σeq : SortedEqns σ ℓ'' ℓv) (X : S → hSet ℓX) → Type _
  Model σeq X =
    Σ[ α ∈ Ops {σ = σ} (λ s → ⟨ X s ⟩) ] Sat σeq (λ s → ⟨ X s ⟩) α

  isPropSat : (σeq : SortedEqns σ ℓ'' ℓv) (X : S → hSet ℓX)
    (α : Ops {σ = σ} (λ s → ⟨ X s ⟩))
    → isProp (Sat σeq (λ s → ⟨ X s ⟩) α)
  isPropSat σeq X α = isPropΠ2 (λ e ρ → X (σeq .eqnSort e) .snd _ _)

-- the points of a pointed algebra, and the pointed algebra on a family
-- of chosen elements
module _ {S : Type ℓS} (V : Type ℓv) (vs : V → S) (X : S → Type ℓX)
  where

  pointsOfˢ : Ops {σ = PointedSigˢ {ℓ' = ℓ'} V vs} X → (v : V) → X (vs v)
  pointsOfˢ α v = α v noArgs

  mkPointsˢ : ((v : V) → X (vs v)) → Ops {σ = PointedSigˢ {ℓ' = ℓ'} V vs} X
  mkPointsˢ ρ v _ = ρ v

-- A model of `σeq [ V , vs ]adjoin` is a model of σeq together with a
-- sorted family of chosen elements.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (V : Type ℓv) (vs : V → S) where

  private
    P : SortedSig S ℓv ℓ'
    P = PointedSigˢ V vs

  module _ (X : S → hSet ℓX) where

    private
      ⟨X⟩ : S → Type ℓX
      ⟨X⟩ s = ⟨ X s ⟩

    ⊕Ops : Ops {σ = σ} ⟨X⟩ → ((v : V) → ⟨X⟩ (vs v))
      → Ops {σ = σ ⊕Sig P} ⟨X⟩
    ⊕Ops β ρ (inl o) = β o
    ⊕Ops β ρ (inr v) = mkPointsˢ V vs ⟨X⟩ ρ v

    ⊕Sat : (β : Ops {σ = σ} ⟨X⟩) (ρ : (v : V) → ⟨X⟩ (vs v))
      → Sat σeq ⟨X⟩ β → Sat (σeq [ V , vs ]adjoin) ⟨X⟩ (⊕Ops β ρ)
    ⊕Sat β ρ sat (inl e) ρ' =
      TmRec-inl σ P ⟨X⟩ (⊕Ops β ρ) ρ' (σeq .lhs e)
      ∙ sat e ρ'
      ∙ sym (TmRec-inl σ P ⟨X⟩ (⊕Ops β ρ) ρ' (σeq .rhs e))

    modelIso : Iso (Model (σeq [ V , vs ]adjoin) X)
                   (Model σeq X × ((v : V) → ⟨X⟩ (vs v)))
    modelIso .Iso.fun (α , sat) =
      ((λ o → α (inl o)) , satl σeq (Pointedˢ V vs) ⟨X⟩ α sat)
      , pointsOfˢ V vs ⟨X⟩ (resr σ P ⟨X⟩ α)
    modelIso .Iso.inv ((β , sat) , ρ) = ⊕Ops β ρ , ⊕Sat β ρ sat
    modelIso .Iso.sec ((β , sat) , ρ) =
      ΣPathP (Σ≡Prop (isPropSat σeq X) refl , refl)
    modelIso .Iso.ret (α , sat) =
      Σ≡Prop (isPropSat (σeq [ V , vs ]adjoin) X)
        (funExt (λ { (inl o) → refl
                   ; (inr v) → funExt (noArgsη (α (inr v))) }))

    withPoints : Model σeq X → ((v : V) → ⟨X⟩ (vs v))
      → Model (σeq [ V , vs ]adjoin) X
    withPoints M ρ = Iso.inv modelIso (M , ρ)

    forgetPoints : Model (σeq [ V , vs ]adjoin) X → Model σeq X
    forgetPoints N = Iso.fun modelIso N .fst

    pointsAt : Model (σeq [ V , vs ]adjoin) X → (v : V) → ⟨X⟩ (vs v)
    pointsAt N = Iso.fun modelIso N .snd

-- The free model on (V , vs), viewed as a model of the extended theory
-- by interpreting each adjoined constant as its generator.
module _ {S : Type ℓS} {σ : SortedSig S ℓ ℓ'} (σeq : SortedEqns σ ℓ'' ℓv)
  (V : Type ℓv) (vs : V → S) where

  private
    ℓF = ℓFree ℓS ℓ ℓ' ℓ'' ℓv

    FreeSet : S → hSet ℓF
    FreeSet s = FreeModel σeq V vs s , trunc

  FreeModelˢ[V] : Model (σeq [ V , vs ]adjoin) FreeSet
  FreeModelˢ[V] =
    withPoints σeq V vs FreeSet (opF , FreeEqns σeq) gen

  FreeObˢ[V] : Category.ob (MOD (σeq [ V , vs ]adjoin) ℓF)
  FreeObˢ[V] = FreeSet , FreeModelˢ[V]

  module _ (N : Category.ob (MOD (σeq [ V , vs ]adjoin) ℓF)) where
    private
      Y : S → Type ℓF
      Y s = ⟨ N .fst s ⟩

      isSetY : (s : S) → isSet (Y s)
      isSetY s = N .fst s .snd

      -- N as a model of σeq together with its chosen points
      α = N .snd .fst
      β = forgetPoints σeq V vs (N .fst) (N .snd) .fst
      sat = forgetPoints σeq V vs (N .fst) (N .snd) .snd
      Nρ = pointsAt σeq V vs (N .fst) (N .snd)

    recC : (s : S) → FreeModel σeq V vs s → Y s
    recC _ = rec σeq isSetY β sat Nρ

    -- the operations of the extended theory: σ's are handled by `rec`
    -- definitionally, the constants by the η-bridge for `⊥*`
    recHom : (o : (σ ⊕Sig PointedSigˢ V vs) .ops)
      (x : (a : (σ ⊕Sig PointedSigˢ V vs) .arities o)
         → FreeModel σeq V vs
             ((σ ⊕Sig PointedSigˢ V vs) .sortOf o a))
      (y : FreeModel σeq V vs
             ((σ ⊕Sig PointedSigˢ V vs) .resultSort o))
      → y ≡ FreeModelˢ[V] .fst o x
      → recC _ y ≡ α o (λ a → recC _ (x a))
    recHom (inl o) x y eq = cong (recC _) eq
    recHom (inr v) x y eq =
      cong (recC _) eq ∙ noArgsη (α (inr v)) (λ a → recC _ (x a))

    isContrHomˢ[V] :
      isContr (ModHom (σeq [ V , vs ]adjoin) ℓF FreeObˢ[V] N)
    isContrHomˢ[V] .fst = recC , recHom , tt*
    isContrHomˢ[V] .snd (f , ϕ , _) =
      Σ≡Prop
        (λ _ → isPropΣ (isPropΠ4 (λ _ _ _ _ → isSetY _ _ _))
                       (λ _ → isPropUnit*))
        (funExt (λ s → funExt (λ x →
          sym (recUniq σeq isSetY β sat Nρ f
                 (λ o → ϕ (inl o))
                 (λ v → ϕ (inr v) noArgs (gen v) refl
                        ∙ sym (noArgsη (α (inr v)) _))
                 x))))

  isInitialFreeObˢ[V] :
    isInitial (MOD (σeq [ V , vs ]adjoin) ℓF) FreeObˢ[V]
  isInitialFreeObˢ[V] = isContrHomˢ[V]

  InitialMODˢ[V] : Initial (MOD (σeq [ V , vs ]adjoin) ℓF)
  InitialMODˢ[V] = FreeObˢ[V] , isInitialFreeObˢ[V]
